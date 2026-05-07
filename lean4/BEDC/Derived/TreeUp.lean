import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

theorem TreeVisibleSpine_extension_ledger {source mid target tail path extended : BHist} :
    GraphContEdge source path mid -> UnaryHistory tail -> Cont mid tail target ->
      Cont path tail extended ->
        GraphContEdge source extended target ∧ GraphContEdge mid tail target ∧
          hsame (append source extended) target := by
  intro edge tailUnary targetRow extendedRow
  have midUnary : UnaryHistory mid :=
    unary_cont_closed edge.left edge.right.left edge.right.right
  have extendedUnary : UnaryHistory extended :=
    unary_cont_closed edge.right.left tailUnary extendedRow
  have sourceExtendedRow : Cont source extended target := by
    cases edge.right.right
    cases targetRow
    cases extendedRow
    exact append_assoc source path tail
  have sameLedger : hsame (append source extended) target := by
    cases edge.right.right
    cases targetRow
    cases extendedRow
    exact (append_assoc source path tail).symm
  exact And.intro
    (And.intro edge.left (And.intro extendedUnary sourceExtendedRow))
    (And.intro
      (And.intro midUnary (And.intro tailUnary targetRow))
      sameLedger)

end BEDC.Derived.TreeUp
