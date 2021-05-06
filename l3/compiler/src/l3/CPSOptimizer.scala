package l3

import scala.collection.mutable.{Map => MutableMap}

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  private case class Count(applied: Int = 0, asValue: Int = 0, blockSet: Int = 0)

  private case class Block(name: Name, dead: Boolean, immutable: Boolean, values: Map[Atom, Atom])

  private case class State(
    census: Map[Name, Count],
    aSubst: Subst[Atom] = emptySubst,
    cSubst: Subst[Name] = emptySubst,
    eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
    cEnv: Map[Name, Cnt] = Map.empty,
    fEnv: Map[Name, Fun] = Map.empty,
    bEnv: Map[Name, Block] = Map.empty) {

    def dead(s: Name): Boolean =
      ! census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0, blockSet = 0))
    def deadBlock(s: Name): Boolean =
      census(s).applied == 0 && census(s).asValue == census(s).blockSet

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)
    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Atom]): State =
      withExp(AtomN(name), prim, args)

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
    def withBlock(blk: Block): State =
      copy(bEnv = bEnv + (blk.name -> blk))
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  private def shrink(tree: Tree, s: State): Tree = tree match {
    case LetP(n, p, _, b) if s.dead(n) && !impure(p) => shrink(b, s)
    case LetP(n, `identity`, Seq(a), b) => shrink(b, s.withASubst(n, a))
    case LetP(n, p, a, b) if s.eInvEnv.contains(p, a map s.aSubst) && !impure(p) && !unstable(p) =>
      shrink(b, s.withASubst(n, s.eInvEnv(p, a map s.aSubst)))
    case LetP(n, p, a, b) if doCFLitV(p, a) =>
      val foldedLit = vEvaluator.apply(p, a map (_.asLiteral.get))
      shrink(b, s.withASubst(n, foldedLit))
    case LetP(n, p, a, b) if doCFSameV(p, a, s) =>
      val foldedAtom = sameArgReduce.apply(p, s.aSubst(a.head))
      shrink(b, s.withASubst(n, foldedAtom))
    case LetP(n, p, Seq(AtomL(l), a), b) if leftNeutral.contains(l, p) => shrink(b, s.withASubst(n, a))
    case LetP(n, p, Seq(a, AtomL(l)), b) if rightNeutral.contains(p, l) => shrink(b, s.withASubst(n, a))
    case LetP(n, p, Seq(AtomL(l), _), b) if leftAbsorbing.contains(l, p) => shrink(b, s.withASubst(n, l))
    case LetP(n, p, Seq(_, AtomL(l)), b) if rightAbsorbing.contains(p, l) => shrink(b, s.withASubst(n, l))
    case LetP(n, p, a, b) if blockAllocTag.isDefinedAt(p) =>
      val tag = blockAllocTag.apply(p)
      val immutable = tag == BlockTag.String || tag == BlockTag.Function
      val dead = s.deadBlock(n)
      val newState = s.withBlock(Block(n, dead, immutable, Map.empty))
      if(dead) shrink(b, newState)
      else LetP(n, p, a map s.aSubst, shrink(b, newState))
    case LetP(n, `blockSet`, Seq(a, i, v), b) if s.aSubst(a).asName.flatMap(s.bEnv.get).nonEmpty =>
      val blk = s.bEnv(s.aSubst(a).asName.get)
      if(blk.dead) shrink(b, s)
      else {
        val newBlk = blk.copy(values = blk.values + (s.aSubst(i) -> s.aSubst(v)))
        LetP(n, blockSet, Seq(a, i, v) map s.aSubst, shrink(b, s.withBlock(newBlk)))
      }
    case LetP(n, `blockGet`, Seq(a, i), b) if s.aSubst(a).asName.flatMap(s.bEnv.get).exists(_.immutable)
                                            && s.bEnv(s.aSubst(a).asName.get).values.contains(s.aSubst(i)) =>
      val value = s.bEnv(s.aSubst(a).asName.get).values(s.aSubst(i))
      shrink(b, s.withASubst(n, value))
    case LetP(n, p, a, b) =>
      val subArgs = a map s.aSubst
      LetP(n, p, subArgs, shrink(b, s.withExp(n, p, subArgs)))

    case LetC(cnts, body) =>
      val nonDead = cnts.filterNot(c => s.dead(c.name))
      val toInline = nonDead.filter(c => s.appliedOnce(c.name))
      val regular = nonDead.filterNot(c => s.appliedOnce(c.name))
      val newState = s.withCnts(toInline)
      val shrunkCnts = regular.map(c => Cnt(c.name, c.args, shrink(c.body, newState)))
      if(shrunkCnts.nonEmpty) LetC(shrunkCnts, shrink(body, newState))
      else shrink(body, newState)

    case LetF(funs, body) =>
      val nonDead = funs.filterNot(f => s.dead(f.name))
      val toInline = nonDead.filter(f => s.appliedOnce(f.name))
      val regular = nonDead.filterNot(f => s.appliedOnce(f.name))
      val newState = s.withFuns(toInline)
      val shrunkFuns = regular.map(f => Fun(f.name, f.retC, f.args, shrink(f.body, newState)))
      if(shrunkFuns.nonEmpty) LetF(shrunkFuns, shrink(body, newState))
      else shrink(body, newState)

    case AppC(cnt, args) if s.cEnv.contains(s.cSubst(cnt)) =>
      val c = s.cEnv(s.cSubst(cnt))
      shrink(c.body, s.withASubst(c.args, args))
    case AppC(cnt, args) => AppC(s.cSubst(cnt), args map s.aSubst)

    case AppF(fun, retC, args) if s.aSubst(fun).asName.nonEmpty && s.fEnv.contains(s.aSubst(fun).asName.get) =>
      val f = s.fEnv(s.aSubst(fun).asName.get)
      shrink(f.body, s.withASubst(f.args, args).withCSubst(f.retC, retC))
    case AppF(fun, retC, args) => AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)

    case If(c, a, t, e) if doCFLitT(c, a) =>
      val foldedLit = cEvaluator.apply(c, a map (_.asLiteral.get))
      if(foldedLit) AppC(s.cSubst(t), Seq())
      else AppC(s.cSubst(e), Seq())
    case If(c, a, t, e) if doCFSameT(c, a, s) =>
      val testResult = sameArgReduceC.apply(c)
      if(testResult) AppC(s.cSubst(t), Seq())
      else AppC(s.cSubst(e), Seq())
    case If(c, a, t, e) => If(c, a map s.aSubst, s.cSubst(t), s.cSubst(e))

    case Halt(arg) => Halt(s.aSubst(arg))
  }

  // Constant folding (CF)
  private def doCFLitV(prim: ValuePrimitive, args: Seq[Atom]): Boolean =
    args.forall(_.asLiteral.nonEmpty) && vEvaluator.isDefinedAt(prim, args map (_.asLiteral.get))
  private def doCFLitT(prim: TestPrimitive, args: Seq[Atom]): Boolean =
    args.forall(_.asLiteral.nonEmpty) && cEvaluator.isDefinedAt(prim, args map (_.asLiteral.get))
  private def doCFSameV(prim: ValuePrimitive, args: Seq[Atom], s: State): Boolean = {
    val subArgs = args map s.aSubst
    subArgs.headOption match {
      case None => false
      case Some(arg) => subArgs.forall(_ == arg) && sameArgReduce.isDefinedAt(prim, arg)
    }
  }
  private def doCFSameT(prim: TestPrimitive, args: Seq[Atom], s: State): Boolean = {
    val subArgs = args map s.aSubst
    subArgs.headOption match {
      case None => false
      case Some(arg) => subArgs.forall(_ == arg) && sameArgReduceC.isDefinedAt(prim)
    }
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(tree: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = {
      (tree: @unchecked) match {
        case LetP(name, prim, args, body) =>
          val name1 = name.copy()
          LetP(name1, prim, args map subV,
               copyT(body, subV + (AtomN(name) -> AtomN(name1)), subC))
        case LetC(cnts, body) =>
          val names = cnts map (_.name)
          val names1 = names map (_.copy())
          val subC1 = subC ++ (names zip names1)
          LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
        case LetF(funs, body) =>
          val names = funs map (_.name)
          val names1 = names map (_.copy())
          val subV1 = subV ++ ((names map AtomN) zip (names1 map AtomN))
          LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
        case AppC(cnt, args) =>
          AppC(subC(cnt), args map subV)
        case AppF(fun, retC, args) =>
          AppF(subV(fun), subC(retC), args map subV)
        case If(cond, args, thenC, elseC) =>
          If(cond, args map subV, subC(thenC), subC(elseC))
        case Halt(arg) =>
          Halt(subV(arg))
      }
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ ((cnt.args map AtomN) zip (args1 map AtomN))
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ ((fun.args map AtomN) zip (args1 map AtomN))
      val AtomN(funName1) = subV(AtomN(fun.name))
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def sameLen[T,U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
        formalArgs.length == actualArgs.length

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        case LetP(name, prim, args, body) => LetP(name, prim, args map s.aSubst, inlineT(body))
        case LetC(cnts, body) =>
          val toInline = cnts.filter(c => size(c.body) <= cntLimit)
          val newState = s.withCnts(toInline)
          val tfCnts = cnts.map(copyC(_, newState.aSubst, newState.cSubst))//cnts.map(c => Cnt(c.name, c.args, inlineT(c.body)(newState)))
          LetC(tfCnts, inlineT(body)(newState))
        case LetF(funs, body) =>
          val toInline = funs.filter(f => size(f.body) <= funLimit)
          val newState = s.withFuns(toInline)
          val tfFuns = funs.map(copyF(_, newState.aSubst, newState.cSubst))//funs.map(f => Fun(f.name, f.retC, f.args, inlineT(f.body)(newState)))
          LetF(tfFuns, inlineT(body)(newState))
        case AppC(cnt, args) if s.cEnv.contains(s.cSubst(cnt)) =>
          val c = s.cEnv(s.cSubst(cnt))
          val newState = s.withASubst(c.args, args)
          copyT(c.body, newState.aSubst, newState.cSubst)
        case AppC(cnt, args) => AppC(s.cSubst(cnt), args map s.aSubst)
        case AppF(fun, retC, args) if s.aSubst(fun).asName.nonEmpty && s.fEnv.contains(s.aSubst(fun).asName.get) =>
          val f = s.fEnv(s.aSubst(fun).asName.get)
          val newState = s.withASubst(f.args, args).withCSubst(f.retC, retC)
          copyT(f.body, newState.aSubst, newState.cSubst)
        case AppF(fun, retC, args) => AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)
        case If(cond, args, thenC, elseC) => If(cond, args map s.aSubst, s.cSubst(thenC), s.cSubst(elseC))
        case Halt(arg) => Halt(s.aSubst(arg))
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(applied = currCount.applied + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incAppUseA(atom: Atom): Unit =
      atom.asName.foreach(incAppUseN(_))

    def incValUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(asValue = currCount.asValue + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incValUseA(atom: Atom): Unit =
      atom.asName.foreach(incValUseN(_))

    def incBlockSetUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(blockSet = currCount.blockSet + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incBlockSetUseA(atom: Atom): Unit =
      atom.asName.foreach(incBlockSetUseN(_))

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(_, `blockSet`, args, body) =>
        incBlockSetUseA(args.head); args foreach incValUseA; addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUseA; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUseN(cnt); args foreach incValUseA
      case AppF(fun, retC, args) =>
        incAppUseA(fun); incValUseN(retC); args foreach incValUseA
      case If(_, args, thenC, elseC) =>
        args foreach incValUseA; incValUseN(thenC); incValUseN(elseC)
      case Halt(arg) =>
        incValUseA(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive
  protected val blockSet: ValuePrimitive
  protected val blockGet: ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean]

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._
  import L3Primitive._

  def apply(tree: Tree): Tree =
    rewrite(tree)

  import scala.language.implicitConversions
  private[this] implicit def l3IntToLit(i: L3Int): Literal = IntLit(i)
  private[this] implicit def intToLit(i: Int): Literal = IntLit(L3Int(i))

  protected val impure: ValuePrimitive => Boolean = Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(t) => t
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength
  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, IntAdd), (1, IntMul), (~0, IntBitwiseAnd), (0, IntBitwiseOr), (0, IntBitwiseXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((IntAdd, 0), (IntSub, 0), (IntMul, 1), (IntDiv, 1),
      (IntShiftLeft, 0), (IntShiftRight, 0),
      (IntBitwiseAnd, ~0), (IntBitwiseOr, 0), (IntBitwiseXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, IntMul), (0, IntDiv),
      (0, IntShiftLeft), (0, IntShiftRight),
      (0, IntBitwiseAnd), (~0, IntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((IntMul, 0), (IntBitwiseAnd, 0), (IntBitwiseOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (IntSub | IntMod | IntBitwiseXOr, _) => AtomL(0)
    case (IntDiv, _) => AtomL(1)
    case (IntBitwiseAnd | IntBitwiseOr, a) => a
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Eq | IntLe => true
    case IntLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (IntAdd, Seq(IntLit(x), IntLit(y))) => x + y
    case (IntSub, Seq(IntLit(x), IntLit(y))) => x - y
    case (IntMul, Seq(IntLit(x), IntLit(y))) => x * y
    case (IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x / y
    case (IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x % y

    case (IntShiftLeft, Seq(IntLit(x), IntLit(y))) => x << y
    case (IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (IntBitwiseOr, Seq(IntLit(x), IntLit(y))) => x | y
    case (IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y

    case (IntToChar, Seq(IntLit(L3Int(x)))) => CharLit(x)
    case (CharToInt, Seq(CharLit(x))) => x
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (Eq, Seq(x, y)) => x == y
    case (BlockP, _) => false
    case (IntP, Seq(IntLit(_))) => true
    case (IntP, _) => false
    case (CharP, Seq(CharLit(_))) => true
    case (CharP, _) => false
    case (BoolP, Seq(BooleanLit(_))) => true
    case (BoolP, _) => false
    case (UnitP, Seq(UnitLit)) => true
    case (UnitP, _) => false
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.LetF => SymbolicCPSTreeModuleLow.LetF) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(tree: LetF): LetF = rewrite(tree) match {
    case tree @ LetF(_, _) => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength
  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((Add, 0), (Sub, 0), (Mul, 1), (Div, 1),
        (ShiftLeft, 0), (ShiftRight, 0),
        (And, ~0), (Or, 0), (XOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div),
        (0, ShiftLeft), (0, ShiftRight),
        (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a) => a
    case (Sub | Mod | XOr, _) => AtomL(0)
    case (Div, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (Add, Seq(x, y)) => x + y
    case (Sub, Seq(x, y)) => x - y
    case (Mul, Seq(x, y)) => x * y
    case (Div, Seq(x, y)) if y.toInt != 0 => x / y
    case (Mod, Seq(x, y)) if y.toInt != 0 => x % y

    case (ShiftLeft,  Seq(x, y)) => x << y
    case (ShiftRight, Seq(x, y)) => x >> y
    case (And, Seq(x, y)) => x & y
    case (Or,  Seq(x, y)) => x | y
    case (XOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (Lt, Seq(x, y)) => x < y
    case (Le, Seq(x, y)) => x <= y
    case (Eq, Seq(x, y)) => x == y
  }
}
