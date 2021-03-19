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
        transformIf(
          prim, as,
          cnt => createBranch(C.AppC(cnt, Seq(C.AtomL(BooleanLit(true))))),
          cnt => createBranch(C.AppC(cnt, Seq(C.AtomL(BooleanLit(false)))))
        )(ctx)
      }
      case S.App(fun, args) =>
        val (name, cnt) = createCont(ctx)
        C.LetC(Seq(cnt), transform(fun) { f => transformSeq(args) { as => C.AppF(f, name, as) } })
      case S.If(S.Prim(prim: L3TestPrimitive, args), thenB, elseB) => transformSeq(args) { as =>
        transformIf(prim, as, transformCreateBranch(thenB), transformCreateBranch(elseB))(ctx)
      }
      case S.If(cond, thenB, elseB) => transform(cond) { a =>
        val args = Seq(a, C.AtomL(BooleanLit(false)))
        transformIf(L3.Eq, args, transformCreateBranch(elseB), transformCreateBranch(thenB))(ctx)
      }
      case S.LetRec(funs, body) =>
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

  private def transformIf(prim: L3TestPrimitive, args: Seq[C.Atom],
                          thenB: Symbol => (Symbol, C.Cnt),
                          elseB: Symbol => (Symbol, C.Cnt))
                         (ctx: C.Atom => C.Tree): C.Tree = {
      val (finN, finC) = createCont(ctx)
      val (thenN, thenC) = thenB(finN)
      val (elseN, elseC) = elseB(finN)
      C.LetC(Seq(finC, thenC, elseC),
        C.If(prim, args, thenN, elseN)
      )
    }

  private def createBranch(branch: C.Tree): (Symbol, C.Cnt) = {
    val name = Symbol.fresh("branch")
    (name, C.Cnt(name, Seq(), branch))
  }

  private def transformCreateBranch(branch: S.Tree)(finN: Symbol): (Symbol, C.Cnt) =
    createBranch(transform(branch) { a => C.AppC(finN, Seq(a)) })

  private def createCont(f: C.Atom => C.Tree): (Symbol, C.Cnt) = {
    val contName = Symbol.fresh("contName")
    val contVar = Symbol.fresh("contVar")
    (contName, C.Cnt(contName, Seq(contVar), f(C.AtomN(contVar))))
  }
}
