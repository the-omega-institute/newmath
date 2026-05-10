import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormExteriorDerivativeLedger_downstream_input_obligation
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
      UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
        Cont d (BHist.e1 BHist.Empty) dplus ∧ hsame probe probe' ∧ hsame tensor tensor' ∧
          hsame scalar scalar' ∧ UnaryHistory antisym ∧ UnaryHistory source ∧
            (hsame dplus BHist.Empty -> False) := by
  intro ledger
  have successorRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty ledger
  exact
    ⟨ledger.left,
      ledger.right.left,
      successorRows.left,
      successorRows.right.left,
      successorRows.right.right.left,
      ledger.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right,
      successorRows.right.right.right⟩

end BEDC.Derived.DiffFormUp
