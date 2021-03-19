package l3

import l3.{L3Primitive => L3}
import l3.{SymbolicCL3TreeModule => S}
import l3.{SymbolicCPSTreeModule => C}

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree =
    transform(tree) { _ =>
      // \v => (halt 0)
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }

  private def transform(tree: S.Tree)(ctx: C.Atom => C.Tree): C.Tree =
    tree match {
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(value) => ctx(C.AtomL(value))
      case S.Halt(tree) => transform(tree) { a => C.Halt(a) }
      case S.Prim(prim: L3ValuePrimitive, args) => transformSeq(args) { as =>
        val name = Symbol.fresh("primVal")
        C.LetP(name, prim, as, ctx(C.AtomN(name)))
      }
      case S.Prim(prim: L3TestPrimitive, args) => transformSeq(args) { as =>
        transformIf(prim, as,
          ifCtx => ifCtx(C.AtomL(BooleanLit(true))),
          elseCtx => elseCtx(C.AtomL(BooleanLit(false)))
        )(ctx)
      }
      case S.App(fun, args) =>
        val (name, cnt) = createCont(ctx)
        C.LetC(Seq(cnt), transform(fun) { f => transformSeq(args) { as => C.AppF(f, name, as) } })
      case S.If(S.Prim(prim: L3TestPrimitive, args), thenB, elseB) => transformSeq(args) { as =>
        transformIf(prim, as, transform(thenB), transform(elseB))(ctx)
      }
      case S.If(cond, thenB, elseB) => transform(cond) { a =>
        val args = Seq(a, C.AtomL(BooleanLit(false)))
        transformIf(L3.Eq, args, transform(elseB), transform(thenB))(ctx)
      }
      case S.LetRec(l3Funs, body) =>
        val cpsFuns = l3Funs.map(transformFun)
        C.LetF(cpsFuns, transform(body)(ctx))
      case S.Let(bndgs, body) =>
        val names = bndgs.map(e => e._1)
        val vals = bndgs.map(e => e._2)
        transformSeq(vals) { as =>
          names.zip(as).foldRight(transform(body)(ctx)) {
            case ((n, a), b) => C.LetP(n, L3.Id, Seq(a), b)
          }
        }
    }

  private def transformSeq(trees: Seq[S.Tree])(ctx: Seq[C.Atom] => C.Tree): C.Tree =
    trees match {
      case Seq(head, tail @_*) => transform(head) { a1 =>
        transformSeq(tail) { as =>
          ctx(a1 +: as)
        }
      }
      case Seq() => ctx(Seq())
    }

  private def transformFun(f: S.Fun): C.Fun = {
    val contName = Symbol.fresh("funContArg")
    val b = transform(f.body) { a => C.AppC(contName, Seq(a)) }
    C.Fun(f.name, contName, f.args, b)
  }

  private def transformIf(prim: L3TestPrimitive, args: Seq[C.Atom],
                          thenB: (C.Atom => C.Tree) => C.Tree,
                          elseB: (C.Atom => C.Tree) => C.Tree)
                         (ctx: C.Atom => C.Tree): C.Tree = {
      val (finN, finC) = createCont(ctx)
      val (thenN, thenC) = createBranch(finN, thenB)
      val (elseN, elseC) = createBranch(finN, elseB)
      C.LetC(Seq(finC, thenC, elseC),
        C.If(prim, args, thenN, elseN)
      )
    }

  private def createBranch(finN: Symbol, branch: (C.Atom => C.Tree) => C.Tree): (Symbol, C.Cnt) = {
    val name = Symbol.fresh("branch")
    (name, C.Cnt(name, Seq(), branch { a => C.AppC(finN, Seq(a)) }))
  }

  private def createCont(f: C.Atom => C.Tree): (Symbol, C.Cnt) = {
    val contName = Symbol.fresh("contName")
    val contVar = Symbol.fresh("contVar")
    (contName, C.Cnt(contName, Seq(contVar), f(C.AtomN(contVar))))
  }
}
