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

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
    return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
    assert(memory_start <= p_addr && p_addr <= memory_end);
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

  size_t heap_words = (size_t) (32 * free_words / 33);
  size_t bitmap_words = (size_t) ceil( heap_words / 32.);

  bitmap = hs;
  heap_start = bitmap + bitmap_words;
}

value_t* memory_allocate(tag_t tag, value_t size, roots_t* roots) {
  assert(free_boundary != NULL);

  const value_t total_size = size + HEADER_SIZE;
  if (free_boundary + total_size > memory_end)
    fail("no memory left (block of size %u requested)", size);

  *free_boundary = header_pack(tag, size);
  value_t* res = free_boundary + HEADER_SIZE;
  free_boundary += total_size;

  return res;
}

void memory_allocate_lb_ob(value_t l_size, value_t o_size, roots_t* roots) {
  roots->Lb = memory_allocate(tag_RegisterFrame, l_size, roots);
  roots->Ob = memory_allocate(tag_RegisterFrame, o_size, roots);
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}
