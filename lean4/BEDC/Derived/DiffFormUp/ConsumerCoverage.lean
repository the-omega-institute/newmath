import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormExteriorDerivative_consumer_coverage
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source consumer
      endpoint : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      UnaryHistory consumer ->
        Cont source consumer endpoint ->
          UnaryHistory domega ∧ UnaryHistory dplus ∧ UnaryHistory endpoint ∧
            hsame dplus (BHist.e1 d) ∧ hsame endpoint (append source consumer) := by
  intro ledger consumerUnary consumerRow
  have degreeRows := DiffFormExteriorDerivativeLedger_degree_raise ledger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledger.right.right.right.right.right.right.right.right.right consumerUnary
      consumerRow
  exact And.intro ledger.right.left
    (And.intro degreeRows.right.left
      (And.intro endpointUnary
        (And.intro degreeRows.right.right consumerRow)))

end BEDC.Derived.DiffFormUp
