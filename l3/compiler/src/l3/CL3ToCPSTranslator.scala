package l3

import l3.{L3Primitive => L3}
import l3.{SymbolicCL3TreeModule => S}
import l3.{SymbolicCPSTreeModule => C}

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree =
    nonTail(tree) { _ =>
      // \v => (halt 0)
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }

  private def nonTail(tree: S.Tree)(ctx: C.Atom => C.Tree): C.Tree = {
    implicit val pos: Position = tree.pos
    tree match {
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(value) => ctx(C.AtomL(value))
      case S.Halt(tree) => nonTail(tree) { a => C.Halt(a) }
      case S.Prim(prim: L3ValuePrimitive, args) => transformSeq(args) { as =>
        val name = Symbol.fresh("primVal")
        C.LetP(name, prim, as, ctx(C.AtomN(name)))
      }
      case S.Prim(prim: L3TestPrimitive, args) => {
        val t = S.Lit(BooleanLit(true))
        val e = S.Lit(BooleanLit(false))
        val cond = S.Prim(prim, args)
        nonTail(S.If(cond, t, e))(ctx)
      }
      case S.App(fun, args) => {
        val (name, cnt) = createCont(ctx)
        C.LetC(Seq(cnt), applyFun(fun, name, args))
      }
      case S.If(c, t, e) => {
        val (finN, finC) = createCont(ctx)
        val (tN, tC) = createBranch(tail(t)(finN))
        val (eN, eC) = createBranch(tail(e)(finN))
        C.LetC(Seq(finC, tC, eC), cond(c)(tN, eN))
      }
      case S.LetRec(l3Funs, body) => {
        val cpsFuns = l3Funs.map(transformFun)
        C.LetF(cpsFuns, nonTail(body)(ctx))
      }
      case S.Let(bndgs, body) => {
        val names = bndgs.map(e => e._1)
        val vals = bndgs.map(e => e._2)
        transformSeq(vals) { as =>
          names.zip(as).foldRight(nonTail(body)(ctx)) {
            case ((n, a), b) => C.LetP(n, L3.Id, Seq(a), b)
          }
        }
      }
    }
  }

  private def tail(tree: S.Tree)(cont: C.Name): C.Tree = {
    implicit val pos: Position = tree.pos
    tree match {
      case S.Ident(name) => applyCont(cont, C.AtomN(name))
      case S.Lit(value) => applyCont(cont, C.AtomL(value))
      case S.Halt(tree) => nonTail(tree) { a => C.Halt(a) }
      case S.Prim(prim: L3ValuePrimitive, args) => transformSeq(args) { as =>
        val name = Symbol.fresh("primVal")
        C.LetP(name, prim, as, applyCont(cont, C.AtomN(name)))
      }
      case S.Prim(prim: L3TestPrimitive, args) => {
        val t = S.Lit(BooleanLit(true))
        val e = S.Lit(BooleanLit(false))
        val cond = S.Prim(prim, args)
        tail(S.If(cond, t, e))(cont)
      }
      case S.App(fun, args) => applyFun(fun, cont, args)
      case S.If(c, t, e) => {
        val (tN, tC) = createBranch(tail(t)(cont))
        val (eN, eC) = createBranch(tail(e)(cont))
        C.LetC(Seq(tC, eC), cond(c)(tN, eN))
      }
      case S.LetRec(l3Funs, body) => {
        val cpsFuns = l3Funs.map(transformFun)
        C.LetF(cpsFuns, tail(body)(cont))
      }
      case S.Let(bndgs, body) => {
        val names = bndgs.map(e => e._1)
        val vals = bndgs.map(e => e._2)
        transformSeq(vals) { as =>
          names.zip(as).foldRight(tail(body)(cont)) {
            case ((n, a), b) => C.LetP(n, L3.Id, Seq(a), b)
          }
        }
      }
    }
  }

  private def cond(tree: S.Tree)(ct: C.Name, cf: C.Name): C.Tree =
    tree match {
      case S.Ident(name) => C.If(L3.Eq, Seq(C.AtomN(name), C.AtomL(BooleanLit(false))), cf, ct)
      case S.Lit(BooleanLit(false)) => C.AppC(cf, Seq())
      case S.Lit(_) => C.AppC(ct, Seq())
      case S.Halt(tree) => nonTail(tree) { a => C.Halt(a) }
      case S.Prim(prim: L3TestPrimitive, args) => transformSeq(args) { as =>
        C.If(prim, as, ct, cf)
      }
      case S.If(S.Lit(BooleanLit(false)), _, e) => cond(e)(ct, cf)
      case S.If(S.Lit(_), t, _) => cond(t)(ct, cf)
      case S.If(c, S.Lit(tl), S.Lit(el)) => {
        val thenN = getBranch(tl, ct, cf)
        val elseN = getBranch(el, ct, cf)
        cond(c)(thenN, elseN)
      }
      case S.If(c, S.Lit(tl), e) => {
        val thenN = getBranch(tl, ct, cf)
        val (elseN, elseC) = createBranch(cond(e)(ct, cf))
        C.LetC(Seq(elseC), cond(c)(thenN, elseN))
      }
      case S.If(c, t, S.Lit(el)) => {
        val (thenN, thenC) = createBranch(cond(t)(ct, cf))
        val elseN = getBranch(el, ct, cf)
        C.LetC(Seq(thenC), cond(c)(thenN, elseN))
      }
      case S.If(c, t, e) => {
        val (tN, tC) = createBranch(cond(t)(ct, cf))
        val (eN, eC) = createBranch(cond(e)(ct, cf))
        C.LetC(Seq(tC, eC), cond(c)(tN, eN))
      }
      case other => nonTail(other) { a =>
        C.If(L3.Eq, Seq(a, C.AtomL(BooleanLit(false))), cf, ct)
      }
    }

  private def applyFun(fun: S.Tree, cont: C.Name, args: Seq[S.Tree]) = {
    nonTail(fun) { f => transformSeq(args) { as => C.AppF(f, cont, as) } }
  }

  private def applyCont(cont: C.Name, atom: C.Atom) = C.AppC(cont, Seq(atom))

  private def transformSeq(trees: Seq[S.Tree])(ctx: Seq[C.Atom] => C.Tree): C.Tree =
    trees match {
      case Seq(head, tail @_*) => nonTail(head) { a1 =>
        transformSeq(tail) { as =>
          ctx(a1 +: as)
        }
      }
      case Seq() => ctx(Seq())
    }

  private def transformFun(f: S.Fun): C.Fun = {
    val contName = Symbol.fresh("funContArg")
    val b = tail(f.body)(contName)
    C.Fun(f.name, contName, f.args, b)
  }

  private def getBranch(lit: C.Literal, ct: C.Name, cf: C.Name): C.Name = lit match {
    case BooleanLit(false) => cf
    case _ => ct
  }

  private def createBranch(branch: C.Tree): (C.Name, C.Cnt) = {
    val name = Symbol.fresh("branch")
    (name, C.Cnt(name, Seq(), branch))
  }

  private def createCont(f: C.Atom => C.Tree): (C.Name, C.Cnt) = {
    val contName = Symbol.fresh("contName")
    val contVar = Symbol.fresh("contVar")
    (contName, C.Cnt(contName, Seq(contVar), f(C.AtomN(contVar))))
  }
}
