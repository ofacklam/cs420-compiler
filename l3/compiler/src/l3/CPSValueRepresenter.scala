package l3

import l3.{SymbolicCPSTreeModule => H}
import l3.{SymbolicCPSTreeModuleLow => L}
import l3.{L3Primitive => L3}
import l3.{CPSValuePrimitive => CPS}
import l3.{CPSTestPrimitive => CPST}

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetP(name, prim, args, body) => translateLetP(name, prim, args, body)
    case H.LetC(cnts, body) => L.LetC(cnts map translateCnt, apply(body))
    case H.LetF(funs, body) => L.LetF(funs map translateFun, apply(body))
    case H.AppC(cnt, args) => L.AppC(cnt, args map rewriteAtom)
    case H.AppF(fun, retC, args) => L.AppF(rewriteAtom(fun), retC, args map rewriteAtom)
    case H.If(cond, args, thenC, elseC) => translateIf(cond, args, thenC, elseC)
    case H.Halt(arg) => untagInt(rewriteAtom(arg)) { u => L.Halt(u) }
  }

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
      case (L3.IntAdd, Seq(a, b)) => tempLetP(CPS.Sub, Seq(a, L.AtomL(1))) { t =>
        L.LetP(name, CPS.Add, Seq(t, b), lBody)
      }
      case (L3.IntSub, Seq(a, b)) => tempLetP(CPS.Add, Seq(a, L.AtomL(1))) { t =>
        L.LetP(name, CPS.Sub, Seq(t, b), lBody)
      }
      case (L3.IntMul, Seq(a, b)) => tempLetP(CPS.Sub, Seq(a, L.AtomL(1))) { t1 =>
        tempLetP(CPS.ShiftRight, Seq(b, L.AtomL(1))) { t2 =>
          tempLetP(CPS.Mul, Seq(t1, t2)) { res =>
            L.LetP(name, CPS.Add, Seq(res, L.AtomL(1)), lBody)
          }
        }
      }
      case (L3.IntDiv, Seq(a, b)) => tempLetP(CPS.Sub, Seq(a, L.AtomL(1))) { t1 =>
        tempLetP(CPS.Sub, Seq(b, L.AtomL(1))) { t2 =>
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
        tempLetP(CPS.Sub, Seq(a, L.AtomL(1))) { t =>
          tempLetP(CPS.ShiftLeft, Seq(t, s)) { res =>
            L.LetP(name, CPS.Add, Seq(res, L.AtomL(1)), lBody)
          }
        }
      }
      case (L3.IntShiftRight, Seq(a, b)) => untagInt(b) { s =>
        tempLetP(CPS.ShiftRight, Seq(a, s)) { res =>
          L.LetP(name, CPS.Or, Seq(res, L.AtomL(1)), lBody)
        }
      }
      case (L3.IntBitwiseAnd, Seq(a, b)) => L.LetP(name, CPS.And, Seq(a, b), lBody)
      case (L3.IntBitwiseOr, Seq(a, b)) => L.LetP(name, CPS.Or, Seq(a, b), lBody)
      case (L3.IntBitwiseXOr, Seq(a, b)) => tempLetP(CPS.XOr, Seq(a, b)) { res =>
        L.LetP(name, CPS.Or, Seq(res, L.AtomL(1)), lBody)
      }
      case (L3.ByteRead, Seq()) => tempLetP(CPS.ByteRead, Seq()) { res => tagInt(name, res, lBody) }
      case (L3.ByteWrite, Seq(v)) => untagInt(v) { u => L.LetP(name, CPS.ByteWrite, Seq(u), lBody) }
      case (L3.IntToChar, Seq(i)) => tempLetP(CPS.ShiftLeft, Seq(i, L.AtomL(2))) { shifted =>
        L.LetP(name, CPS.Add, Seq(shifted, L.AtomL(2)), lBody)
      }
      case (L3.CharToInt, Seq(c)) => L.LetP(name, CPS.ShiftRight, Seq(c, L.AtomL(2)), lBody)
      case (L3.Id, Seq(n)) => L.LetP(name, CPS.Id, Seq(n), lBody)
    }
  }

  private def translateIf(cond: H.TestPrimitive,
                          args: Seq[H.Atom],
                          thenC: H.Name, elseC: H.Name): L.Tree = {
    val lArgs = args map rewriteAtom
    (cond, lArgs) match {
      case (L3.BlockP, Seq(b)) => tempLetP(CPS.And, Seq(b, L.AtomL(3))) { t =>
        L.If(CPST.Eq, Seq(t, L.AtomL(0)), thenC, elseC)
      }
      case (L3.IntP, Seq(i)) => tempLetP(CPS.And, Seq(i, L.AtomL(1))) { t =>
        L.If(CPST.Eq, Seq(t, L.AtomL(1)), thenC, elseC)
      }
      case (L3.IntLt, Seq(a, b)) => L.If(CPST.Lt, Seq(a, b), thenC, elseC)
      case (L3.IntLe, Seq(a, b)) => L.If(CPST.Le, Seq(a, b), thenC, elseC)
      case (L3.CharP, Seq(c)) => tempLetP(CPS.And, Seq(c, L.AtomL(7))) { t =>
        L.If(CPST.Eq, Seq(t, L.AtomL(6)), thenC, elseC)
      }
      case (L3.BoolP, Seq(b)) => tempLetP(CPS.And, Seq(b, L.AtomL(15))) { t =>
        L.If(CPST.Eq, Seq(t, L.AtomL(10)), thenC, elseC)
      }
      case (L3.UnitP, Seq(u)) => tempLetP(CPS.And, Seq(u, L.AtomL(15))) { t =>
        L.If(CPST.Eq, Seq(t, L.AtomL(2)), thenC, elseC)
      }
      case (L3.Eq, Seq(a, b)) => L.If(CPST.Eq, Seq(a, b), thenC, elseC)
    }
  }

  private def translateFun(f: H.Fun): L.Fun = L.Fun(f.name, f.retC, f.args, apply(f.body))

  private def translateCnt(c: H.Cnt): L.Cnt = L.Cnt(c.name, c.args, apply(c.body))

  private def rewriteAtom(a: H.Atom): L.Atom = a match {
    case H.AtomN(n) => L.AtomN(n)
    case H.AtomL(IntLit(i)) => L.AtomL((i.toInt << 1) | 1)
    case H.AtomL(CharLit(c)) => L.AtomL((c << 3) | 6)
    case H.AtomL(BooleanLit(true)) => L.AtomL(26)
    case H.AtomL(BooleanLit(false)) => L.AtomL(10)
    case H.AtomL(UnitLit) => L.AtomL(2)
  }

  private def untagInt(a: L.Atom)(body: L.Atom => L.Tree): L.Tree =
    tempLetP(CPS.ShiftRight, Seq(a, L.AtomL(1)))(body)

  private def tagInt(name: L.Name, u: L.Atom, body: L.Tree): L.Tree =
    tempLetP(CPS.ShiftLeft, Seq(u, L.AtomL(1))) { t =>
      L.LetP(name, CPS.Add, Seq(t, L.AtomL(1)), body)
    }

  private def tempLetP(prim: L.ValuePrimitive, args: Seq[L.Atom])(body: L.Atom => L.Tree): L.Tree = {
    val tmp = Symbol.fresh("tmp")
    L.LetP(tmp, prim, args, body(L.AtomN(tmp)))
  }
}
