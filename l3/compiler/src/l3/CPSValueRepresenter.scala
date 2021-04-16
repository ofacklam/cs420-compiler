package l3

import l3.{SymbolicCPSTreeModule => H}
import l3.{SymbolicCPSTreeModuleLow => L}
import l3.{L3Primitive => L3}
import l3.{CPSValuePrimitive => CPS}
import l3.{CPSTestPrimitive => CPST}

object CPSValueRepresenter extends (H.Tree => L.Tree) {

  type Env = Map[L.Name, (L.Name, Seq[L.Name])]

  /**
   * Translates high-level to low-level CPS tree
   */
  def apply(tree: H.Tree): L.Tree = translate(tree, Map.empty)

  /**
   * Translates a high-level CPS tree to a low-level tree, keeping track of the environment
   */
  def translate(tree: H.Tree, env: Env): L.Tree = tree match {
    case H.LetP(name, prim, args, body) => translateLetP(name, prim, args, body, env)
    case H.LetC(cnts, body) => L.LetC(cnts.map(rewriteCnt(_, env)), translate(body, env))
    case H.LetF(funs, body) => translateLetF(funs, body, env)
    case H.AppC(cnt, args) => L.AppC(cnt, args map rewriteAtom)
    case H.AppF(fun, retC, args) => translateAppF(fun, retC, args, env)
    case H.If(cond, args, thenC, elseC) => translateIf(cond, args, thenC, elseC)
    case H.Halt(arg) => untagInt(rewriteAtom(arg)) { u => L.Halt(u) }
  }

  /**
   * Translates all LetP clauses, treating each possible ValuePrimitive case separately
   */
  private def translateLetP(name: H.Name,
                            prim: H.ValuePrimitive,
                            args: Seq[H.Atom],
                            body: H.Tree,
                            env: Env): L.Tree = {
    val lArgs = args map rewriteAtom
    val lBody = translate(body, env)
    (prim, lArgs) match {
      case (L3.BlockAlloc(tag), Seq(a)) => untagInt(a) { u =>
        L.LetP(name, CPS.BlockAlloc(tag), Seq(u), lBody)
      }
      case (L3.BlockTag, Seq(a)) => tempLetP(CPS.BlockTag, Seq(a)) { u =>
        tagInt(name, u, lBody)
      }
      case (L3.BlockLength, Seq(a)) => tempLetP(CPS.BlockLength, Seq(a)) { u =>
        tagInt(name, u, lBody)
      }
      case (L3.BlockGet, Seq(b, n)) => untagInt(n) { idx =>
        L.LetP(name, CPS.BlockGet, Seq(b, idx), lBody)
      }
      case (L3.BlockSet, Seq(b, n, v)) => untagInt(n) { idx =>
        L.LetP(name, CPS.BlockSet, Seq(b, idx, v), lBody)
      }
      case (L3.IntAdd, Seq(a, b)) => decrement(a) { t =>
        L.LetP(name, CPS.Add, Seq(t, b), lBody)
      }
      case (L3.IntSub, Seq(a, b)) => increment(a) { t =>
        L.LetP(name, CPS.Sub, Seq(t, b), lBody)
      }
      case (L3.IntMul, Seq(a, b)) => decrement(a) { t1 =>
        shiftRight1(b) { t2 =>
          tempLetP(CPS.Mul, Seq(t1, t2)) { res =>
            incrementBind(name, res, lBody)
          }
        }
      }
      case (L3.IntDiv, Seq(a, b)) => decrement(a) { t1 =>
        decrement(b) { t2 =>
          tempLetP(CPS.Div, Seq(t1, t2)) { res =>
            tagInt(name, res, lBody)
          }
        }
      }
      case (L3.IntMod, Seq(a, b)) => decrement(a) { t1 =>
        decrement(b) { t2 =>
          tempLetP(CPS.Mod, Seq(t1, t2)) { res =>
            incrementBind(name, res, lBody)
          }
        }
      }
      case (L3.IntShiftLeft, Seq(a, b)) => untagInt(b) { s =>
        decrement(a) { t =>
          tempLetP(CPS.ShiftLeft, Seq(t, s)) { res =>
            incrementBind(name, res, lBody)
          }
        }
      }
      case (L3.IntShiftRight, Seq(a, b)) => untagInt(b) { s =>
        tempLetP(CPS.ShiftRight, Seq(a, s)) { res =>
          L.LetP(name, CPS.Or, Seq(res, cst(1)), lBody)
        }
      }
      case (L3.IntBitwiseAnd, Seq(a, b)) => L.LetP(name, CPS.And, Seq(a, b), lBody)
      case (L3.IntBitwiseOr, Seq(a, b)) => L.LetP(name, CPS.Or, Seq(a, b), lBody)
      case (L3.IntBitwiseXOr, Seq(a, b)) => tempLetP(CPS.XOr, Seq(a, b)) { res =>
        L.LetP(name, CPS.Or, Seq(res, cst(1)), lBody)
      }
      case (L3.ByteRead, Seq()) => tempLetP(CPS.ByteRead, Seq()) { res => tagInt(name, res, lBody) }
      case (L3.ByteWrite, Seq(v)) => untagInt(v) { u => L.LetP(name, CPS.ByteWrite, Seq(u), lBody) }
      case (L3.IntToChar, Seq(i)) => tempLetP(CPS.ShiftLeft, Seq(i, L.AtomL(2))) { shifted =>
        L.LetP(name, CPS.Or, Seq(shifted, cstBits(1, 0)), lBody)
      }
      case (L3.CharToInt, Seq(c)) => L.LetP(name, CPS.ShiftRight, Seq(c, L.AtomL(2)), lBody)
      case (L3.Id, Seq(n)) => L.LetP(name, CPS.Id, Seq(n), lBody)
    }
  }

  /**
   * Translate function declarations by doing closure conversion (define worker + wrapper + create environment)
   */
  private def translateLetF(funs: Seq[H.Fun], body: H.Tree, env: Env): L.Tree = {
    // Names
    val funNames = funs.map(_.name).toIndexedSeq
    val workerNames = funNames.map[L.Name](fn => Symbol.fresh(s"${fn.name}_worker"))
    val wrapperNames = funNames.map[L.Name](fn => Symbol.fresh(s"${fn.name}_wrapper"))

    // Compute free variables
    val startEnv = (funNames zip workerNames).foldLeft(env){
      case (e, (fn, wn)) => e.updated(fn, (wn, Seq()))
    }
    val newEnv = fixedPoint(startEnv){ tmpEnv =>
      val fvs = funs.map(freeVariables(_, tmpEnv).toSeq)
      fvs.zipWithIndex.foldLeft(tmpEnv){
        case (e, (fv, i)) => e.updated(funNames(i), (workerNames(i), fv))
      }
    }
    val freeVars = funNames map { fn =>
      newEnv.get(fn).map(_._2).getOrElse(Seq())
    }

    // Create workers
    val workers = (funs lazyZip workerNames lazyZip freeVars) map {
      case (f, wn, fvs) => createWorker(f, wn, fvs, newEnv)
    }
    val wrappers = (funs lazyZip wrapperNames lazyZip workerNames lazyZip freeVars) map {
      case (f, wrapper, worker, fvs) => createWrapper(f, wrapper, worker, fvs)
    }

    // Create closures
    val lBody = translate(body, newEnv)
    val blocksInit = (funNames lazyZip wrapperNames lazyZip freeVars).foldRight(lBody) {
      case ((fn, wn, fvs), b) => initClosure(fn, wn, fvs)(b)
    }
    val blocksCreation = (funNames zip freeVars).foldRight(blocksInit) {
      case ((fn, fvs), b) => createClosure(fn, fvs)(b)
    }

    L.LetF(workers ++: wrappers, blocksCreation)
  }

  /**
   * Translate function applications by applying worker or extracting wrapper from closure
   */
  private def translateAppF(f: H.Atom, c: L.Name, args: Seq[H.Atom], env: Env): L.Tree = {
    val lArgs = args.map(rewriteAtom)
    val lFun = rewriteAtom(f)

    lFun.asName.flatMap(env.get) match {
      case Some((worker, fvs)) => L.AppF(L.AtomN(worker), c, lArgs ++: fvs.map(L.AtomN))
      case None => tempLetP(CPS.BlockGet, Seq(lFun, cst(0))) {
        wrapper => L.AppF(wrapper, c, lFun +: lArgs)
      }
    }
  }

  /**
   * Translates all If clauses, treating each possible TestPrimitive case separately
   */
  private def translateIf(cond: H.TestPrimitive,
                          args: Seq[H.Atom],
                          thenC: H.Name, elseC: H.Name): L.Tree = {
    val lArgs = args map rewriteAtom
    (cond, lArgs) match {
      case (L3.BlockP, Seq(b)) => tempLetP(CPS.And, Seq(b, cstBits(1, 1))) { t =>
        L.If(CPST.Eq, Seq(t, cstBits(0, 0)), thenC, elseC)
      }
      case (L3.IntP, Seq(i)) => tempLetP(CPS.And, Seq(i, cstBits(1))) { t =>
        L.If(CPST.Eq, Seq(t, cstBits(1)), thenC, elseC)
      }
      case (L3.IntLt, Seq(a, b)) => L.If(CPST.Lt, Seq(a, b), thenC, elseC)
      case (L3.IntLe, Seq(a, b)) => L.If(CPST.Le, Seq(a, b), thenC, elseC)
      case (L3.CharP, Seq(c)) => tempLetP(CPS.And, Seq(c, cstBits(1, 1, 1))) { t =>
        L.If(CPST.Eq, Seq(t, cstBits(1, 1, 0)), thenC, elseC)
      }
      case (L3.BoolP, Seq(b)) => tempLetP(CPS.And, Seq(b, cstBits(1, 1, 1, 1))) { t =>
        L.If(CPST.Eq, Seq(t, cstBits(1, 0, 1, 0)), thenC, elseC)
      }
      case (L3.UnitP, Seq(u)) => tempLetP(CPS.And, Seq(u, cstBits(1, 1, 1, 1))) { t =>
        L.If(CPST.Eq, Seq(t, cstBits(0, 0, 1, 0)), thenC, elseC)
      }
      case (L3.Eq, Seq(a, b)) => L.If(CPST.Eq, Seq(a, b), thenC, elseC)
    }
  }

  /**
   * Translate continuation definitions by recursively translating the body
   */
  private def rewriteCnt(c: H.Cnt, env: Env): L.Cnt = L.Cnt(c.name, c.args, translate(c.body, env))

  /**
   * Translate each possible atom
   */
  private def rewriteAtom(a: H.Atom): L.Atom = a match {
    case H.AtomN(n) => L.AtomN(n)
    case H.AtomL(IntLit(i)) => cst((i.toInt << 1) | bitsToIntMSBF(1))
    case H.AtomL(CharLit(c)) => cst((c << 3) | bitsToIntMSBF(1, 1, 0))
    case H.AtomL(BooleanLit(true)) => cstBits(1, 1, 0, 1, 0)
    case H.AtomL(BooleanLit(false)) => cstBits(0, 1, 0, 1, 0)
    case H.AtomL(UnitLit) => cstBits(0, 0, 1, 0)
  }

  /*****************************************
   * HELPER FUNCTIONS for code refactoring *
   *****************************************/
  private def tempLetP(prim: L.ValuePrimitive, args: Seq[L.Atom])(body: L.Atom => L.Tree): L.Tree = {
    val tmp = Symbol.fresh("tmp")
    L.LetP(tmp, prim, args, body(L.AtomN(tmp)))
  }

  private def increment(a: L.Atom)(body: L.Atom => L.Tree): L.Tree =
    tempLetP(CPS.Add, Seq(a, cst(1)))(body)

  private def incrementBind(name: L.Name, u: L.Atom, body: L.Tree): L.Tree =
    L.LetP(name, CPS.Add, Seq(u, cst(1)), body)

  private def decrement(a: L.Atom)(body: L.Atom => L.Tree): L.Tree =
    tempLetP(CPS.Sub, Seq(a, cst(1)))(body)

  private def shiftLeft1(a: L.Atom)(body: L.Atom => L.Tree): L.Tree =
    tempLetP(CPS.ShiftLeft, Seq(a, cst(1)))(body)

  private def shiftRight1(a: L.Atom)(body: L.Atom => L.Tree): L.Tree =
    tempLetP(CPS.ShiftRight, Seq(a, cst(1)))(body)

  private def untagInt(a: L.Atom)(body: L.Atom => L.Tree): L.Tree =
    shiftRight1(a)(body)

  private def tagInt(name: L.Name, u: L.Atom, body: L.Tree): L.Tree =
    shiftLeft1(u) { t =>
      incrementBind(name, t, body)
    }

  private def cst(v: Int): L.AtomL = L.AtomL(v)

  private def cstBits(bits: Int*): L.AtomL = cst(bitsToIntMSBF(bits: _*))

  /**
   * Free variable calculation
   */
  private def freeVariables(tree: H.Tree, env: Env): Set[H.Name] = tree match {
    case H.LetP(n, _, args, b) => (freeVariables(b, env) - n) | flattenSets(args map freeVariables)
    case H.LetC(cnts, b) => flattenSets(cnts.map(freeVariables(_, env))) | freeVariables(b, env)
    case H.LetF(funs, b) =>
      val funFreeVars = flattenSets(funs.map(freeVariables(_, env)))
      val bodyFreeVars = freeVariables(b, env)
      (funFreeVars | bodyFreeVars) &~ funs.map(_.name).toSet
    case H.AppC(_, args) => flattenSets(args map freeVariables)
    case H.AppF(f, _, args) =>
      val argsFreeVars = flattenSets(args map freeVariables)
      val additionalFreeVars = f.asName.flatMap(fn => env.get(fn)) match {
        case None => freeVariables(f)
        case Some((_, fvs)) => fvs.toSet
      }
      argsFreeVars | additionalFreeVars
    case H.If(_, args, _, _) => flattenSets(args map freeVariables)
    case H.Halt(a) => freeVariables(a)
  }

  private def freeVariables(c: H.Cnt, env: Env): Set[H.Name] =
    freeVariables(c.body, env) &~ c.args.toSet

  private def freeVariables(f: H.Fun, env: Env): Set[H.Name] =
    freeVariables(f.body, env) &~ f.args.toSet

  private def freeVariables(atom: H.Atom): Set[H.Name] = atom match {
    case H.AtomL(_) => Set()
    case H.AtomN(n) => Set(n)
  }

  private def flattenSets[A](in: Seq[Set[A]]): Set[A] =
    in.fold(Set.empty) {
      case (a, b) => a | b
    }

  /**
   * Variable substitution
   */
  private def substitute(tree: L.Tree, s: Subst[L.Name]): L.Tree = {
    def substT(tree: L.Tree): L.Tree = tree match {
      case L.LetP(name, prim, args, body) => L.LetP(name, prim, args map substA, substT(body))
      case L.LetC(cnts, body) => L.LetC(cnts map substC, substT(body))
      case L.LetF(funs, body) => L.LetF(funs map substF, substT(body))
      case L.AppC(cnt, args) => L.AppC(cnt, args map substA)
      case L.AppF(fun, retC, args) => L.AppF(substA(fun), retC, args map substA)
      case L.If(cond, args, thenC, elseC) => L.If(cond, args map substA, thenC, elseC)
      case L.Halt(arg) => L.Halt(substA(arg))
    }

    def substC(cnt: L.Cnt): L.Cnt = // code for continuation definitions
      L.Cnt(cnt.name, cnt.args, substT(cnt.body))

    def substF(fun: L.Fun): L.Fun = // code for function definitions
      L.Fun(fun.name, fun.retC, fun.args, substT(fun.body))

    def substA(atom: L.Atom): L.Atom = atom match { // code for atoms
      case L.AtomL(l) => L.AtomL(l)
      case L.AtomN(n) => L.AtomN(s.apply(n))
    }

    substT(tree)
  }

  /**
   * Closure conversion helpers
   */
  def createWorker(f: H.Fun, w: L.Name, fvs: Seq[L.Name], env: Env): L.Fun = {
    val newArgs = for (_ <- fvs) yield Symbol.fresh("newArg")
    val lBody = translate(f.body, env)

    val substitution = subst(fvs, newArgs)
    val sBody = substitute(lBody, substitution)

    L.Fun(w, f.retC, f.args :++ newArgs, sBody)
  }

  def createWrapper(f: H.Fun, wrapper: L.Name, worker: L.Name, fvs: Seq[L.Name]): L.Fun = {
    val envName = Symbol.fresh("env")
    val args = f.args.map(_.copy())
    val retC = f.retC.copy()

    val bvs = for (_ <- fvs) yield Symbol.fresh("boundVar")
    val body = L.AppF(L.AtomN(worker), retC, (args ++: bvs).map(L.AtomN))

    val wrapperBody = bvs.zipWithIndex.foldRight[L.Tree](body) {
      case ((bv, i), b) => L.LetP(bv, CPS.BlockGet, Seq(L.AtomN(envName), cst(i + 1)), b)
    }
    L.Fun(wrapper, retC, envName +: args, wrapperBody)
  }

  def createClosure(name: L.Name, fvs: Seq[L.Name])(body: L.Tree): L.Tree = {
    L.LetP(name, CPS.BlockAlloc(BlockTag.Function.id), Seq(cst(fvs.size + 1)), body)
  }

  def initClosure(name: L.Name, wrapper: L.Name, fvs: Seq[L.Name])(body: L.Tree): L.Tree = {
    val closure = L.AtomN(name)
    (wrapper +: fvs).zipWithIndex.foldRight(body) {
      case ((n, i), b) => L.LetP(Symbol.fresh("blockSet"), CPS.BlockSet, Seq(closure, cst(i), L.AtomN(n)), b)
    }
  }

}
