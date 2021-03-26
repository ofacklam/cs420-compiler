package l3

import l3.{SymbolicCPSTreeModule => H}
import l3.{SymbolicCPSTreeModuleLow => L}
import l3.{L3Primitive => L3}
import l3.{CPSValuePrimitive => CPS}
import l3.{CPSTestPrimitive => CPST}

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  /**
   * Translates a high-level CPS tree to a low-level tree
   */
  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetP(name, prim, args, body) => translateLetP(name, prim, args, body)
    case H.LetC(cnts, body) => L.LetC(cnts map translateCnt, apply(body))
    case H.LetF(funs, body) => L.LetF(funs map translateFun, apply(body))
    case H.AppC(cnt, args) => L.AppC(cnt, args map rewriteAtom)
    case H.AppF(fun, retC, args) => L.AppF(rewriteAtom(fun), retC, args map rewriteAtom)
    case H.If(cond, args, thenC, elseC) => translateIf(cond, args, thenC, elseC)
    case H.Halt(arg) => untagInt(rewriteAtom(arg)) { u => L.Halt(u) }
  }

  /**
   * Translates all LetP clauses, treating each possible ValuePrimitive case separately
   */
  private def translateLetP(name: H.Name,
                            prim: H.ValuePrimitive,
                            args: Seq[H.Atom],
                            body: H.Tree): L.Tree = {
    val lArgs = args map rewriteAtom
    val lBody = apply(body)
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
      case (L3.IntMod, Seq(a, b)) => untagInt(a) { t1 =>
        untagInt(b) { t2 => // TODO
          tempLetP(CPS.Mod, Seq(t1, t2)) { res =>
            tagInt(name, res, lBody)
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
   * Translate function definitions by recursively translating the body
   */
  private def translateFun(f: H.Fun): L.Fun = L.Fun(f.name, f.retC, f.args, apply(f.body))

  /**
   * Translate continuation definitions by recursively translating the body
   */
  private def translateCnt(c: H.Cnt): L.Cnt = L.Cnt(c.name, c.args, apply(c.body))

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
  private def cstBits(bits: Int*): L.AtomL = cst(bitsToIntMSBF(bits :_*))
}
