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
    }
}
