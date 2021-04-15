package l3

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => LetF) {
  def apply(tree: Tree): LetF = tree match {
    case LetP(name, prim, args, body) =>
      val t = apply(body)
      LetF(t.funs, LetP(name, prim, args, t.body))
    case LetC(cnts, body) =>
      val t = apply(body)
      val hoisted = cnts map hoistCnt
      val funs = t.funs ++: hoisted.flatMap(_._1)
      val newCnts = hoisted.map(_._2)
      LetF(funs, LetC(newCnts, t.body))
    case LetF(funs, body) =>
      val t = apply(body)
      val hoisted = funs map hoistFun
      val newFuns = hoisted.flatten :++ t.funs
      LetF(newFuns, t.body)
    case other => LetF(Seq(), other)
  }

  private def hoistCnt(c: Cnt): (Seq[Fun], Cnt) = {
    val t = apply(c.body)
    (t.funs, Cnt(c.name, c.args, t.body))
  }

  private def hoistFun(f: Fun): Seq[Fun] = {
    val t = apply(f.body)
    Fun(f.name, f.retC, f.args, t.body) +: t.funs
  }
}
