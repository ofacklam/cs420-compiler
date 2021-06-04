#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>

#include "memory.h"
#include "fail.h"

static value_t* memory_start = NULL;
static value_t* memory_end = NULL;
static value_t* bitmap = NULL;
static value_t* heap_start = NULL;

#define HEADER_SIZE 1
#define MIN_BLOCK_SIZE 1
#define BITS_PER_WORD (8 * sizeof(value_t))
#define FREE_LIST_SIZE 32

static value_t free_list[FREE_LIST_SIZE]; // points to the block start virtual address

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
    return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
    assert((void*)memory_start <= p_addr && p_addr <= (void*)memory_end);
    return (value_t)((char*)p_addr - (char*)memory_start);
}

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

// Bitmap management

static uint8_t bitmap_is_set(const value_t* block) {
    assert(block >= heap_start);
    value_t mem_offset = (value_t) (block - heap_start);
    value_t bitmap_idx = mem_offset / BITS_PER_WORD;
    uint8_t bitmap_offset = mem_offset % BITS_PER_WORD;
    return (bitmap[bitmap_idx] >> bitmap_offset) & 0x01;
}

static void bitmap_set(const value_t* block) {
    assert(block >= heap_start);
    value_t mem_offset = (value_t) (block - heap_start);
    value_t bitmap_idx = mem_offset / BITS_PER_WORD;
    uint8_t bitmap_offset = mem_offset % BITS_PER_WORD;
    bitmap[bitmap_idx] |= (1u << bitmap_offset);
}

static void bitmap_clear(const value_t* block) {
    assert(block >= heap_start);
    value_t mem_offset = (value_t) (block - heap_start);
    value_t bitmap_idx = mem_offset / BITS_PER_WORD;
    uint8_t bitmap_offset = mem_offset % BITS_PER_WORD;
    bitmap[bitmap_idx] &= ~(1u << bitmap_offset);
}

// Free list management

static void free_list_insert(value_t* block) {
    value_t size = memory_get_block_size(block);
    if(size >= FREE_LIST_SIZE)
        size = FREE_LIST_SIZE - 1;
    value_t old_head = free_list[size];
    *block = old_head;
    free_list[size] = addr_p_to_v(block);
}

static void free_list_remove(const value_t* block, value_t* prev_block) {
    value_t next_block = *block;
    *prev_block = next_block;
}

static value_t* free_list_next(const value_t* block) {
    return addr_v_to_p(*block);
}

static value_t* free_list_find(value_t size) {
    value_t start_index = size < FREE_LIST_SIZE ? size : FREE_LIST_SIZE - 1;

    for(value_t k = start_index; k < FREE_LIST_SIZE; k++) {
        value_t* prev_block = &free_list[k];
        value_t* block;
        while((block = free_list_next(prev_block)) != memory_start) {
            if(memory_get_block_size(block) >= size) {
                free_list_remove(block, prev_block);
                return block;
            }
            prev_block = block;
        }
    }

    return memory_start;
}

// Allocation / de-allocation

static value_t* try_allocate(tag_t tag, value_t size) {
    // find appropriate block
    value_t* block = free_list_find(size);
    if(block == memory_start) // no block available
        return memory_start;

    // split the block
    value_t additional_space = memory_get_block_size(block) - size;
    if(additional_space > 0) {
        value_t* split_block = block + size + HEADER_SIZE;
        split_block[-HEADER_SIZE] = header_pack(tag_None, additional_space - HEADER_SIZE);
        if(additional_space >= HEADER_SIZE + MIN_BLOCK_SIZE) { // enough space for a real block -> add to free list
            free_list_insert(split_block);
        }
    }

    // update bitmap
    bitmap_set(block);

    // set header
    block[-HEADER_SIZE] = header_pack(tag, size);

    // clean block
    for(value_t k = 0; k < size; k++)
        block[k] = 0;

    return block;
}

static void mark(value_t* block) {
    if(block < heap_start || block >= memory_end || !bitmap_is_set(block)) // not allocated or already visited block
        return;

    bitmap_clear(block);
    value_t size = memory_get_block_size(block);

    for(value_t k = 0; k < size; k++) {
        value_t potential_pointer = block[k];
        if(0 == (potential_pointer & 0x03)) // it is of pointer form
            mark(addr_v_to_p(potential_pointer));
    }
}

static value_t* next_block(value_t* block) {
    return block + memory_get_block_size(block) + HEADER_SIZE;
}

static uint8_t is_allocated_and_reachable(value_t* block) {
    tag_t tag = memory_get_block_tag(block);
    uint8_t bit_set = bitmap_is_set(block);
    return tag != tag_None && !bit_set;
}

static void sweep() {
    // clear all free lists
    for(int k = 0; k < FREE_LIST_SIZE; k++)
        free_list[k] = 0;

    // sweep the entire heap
    value_t* current_block = heap_start + HEADER_SIZE;
    while(current_block < memory_end) {
        // 2 cases
        if(is_allocated_and_reachable(current_block)) { // allocated, reachable block -> keep it
            bitmap_set(current_block);
        } else { // free block -> coalesce adjacent & add to free list
            value_t free_size = 0;
            value_t* current_free = current_block;
            while(current_free < memory_end && !is_allocated_and_reachable(current_free)) {
                bitmap_clear(current_free);
                free_size += memory_get_block_size(current_free) + HEADER_SIZE;
                current_free = next_block(current_free);
            }

            free_size -= HEADER_SIZE;
            current_block[-HEADER_SIZE] = header_pack(tag_None, free_size);

            if(free_size >= MIN_BLOCK_SIZE) // add to free list if large enough
                free_list_insert(current_block);
        }

        current_block = next_block(current_block);
    }
}

static void collect_garbage(roots_t* roots) {
    // mark from all roots
    mark(roots->Ib);
    mark(roots->Lb);
    mark(roots->Ob);

    // sweep
    sweep();
}

// Interface implementation

char* memory_get_identity() {
  return "mark-and-sweep GC";
}

void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = memory_start + (total_byte_size / sizeof(value_t));
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);
  memory_start = memory_end = bitmap = heap_start = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* hs) {
  assert(bitmap == NULL && heap_start == NULL);
  long free_words = memory_end - (value_t*) hs;
  if(free_words <= 0)
      fail("No memory left for heap");

  value_t heap_words = BITS_PER_WORD * (value_t) free_words / (BITS_PER_WORD + 1);
  value_t bitmap_words = (heap_words / BITS_PER_WORD) + (heap_words % BITS_PER_WORD != 0);

  bitmap = hs;
  heap_start = bitmap + bitmap_words;

  value_t* whole_memory_block = heap_start + HEADER_SIZE;
  whole_memory_block[-HEADER_SIZE] = header_pack(tag_None, heap_words - HEADER_SIZE);
  free_list_insert(whole_memory_block);
}

value_t* memory_allocate(tag_t tag, value_t size, roots_t* roots) {
  assert(heap_start != NULL);

  // 1st allocation -> return if success
  value_t* block = try_allocate(tag, size);
  if (block != memory_start)
    return block;

  // in case of out of memory -> do garbage collection & retry
  collect_garbage(roots);
  block = try_allocate(tag, size);
  if (block == memory_start)
    fail("no memory left (block of size %u requested)", size);

  return block;
}

void memory_allocate_lb_ob(value_t l_size, value_t o_size, roots_t* roots) {
  value_t total_size = l_size + o_size + HEADER_SIZE;
  value_t* big_block = memory_allocate(tag_RegisterFrame, total_size, roots);

  value_t* lb = big_block;
  lb[-HEADER_SIZE] = header_pack(tag_RegisterFrame, l_size);
  bitmap_set(lb);
  roots->Lb = lb;

  value_t* ob = next_block(lb);
  ob[-HEADER_SIZE] = header_pack(tag_RegisterFrame, o_size);
  bitmap_set(ob);
  roots->Ob = ob;
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-HEADER_SIZE]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-HEADER_SIZE]);
}
