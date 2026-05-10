import BEDC.Derived.BilinFormUp

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BilinFormBHistObligationSurface_empty_ledger_source_empty
    {left right scalar additive endpoint scalarLedger ledger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame ledger BHist.Empty ->
        hsame left BHist.Empty ∧ hsame right BHist.Empty ∧ hsame scalar BHist.Empty ∧
          hsame additive BHist.Empty := by
  intro surface ledgerEmpty
  have endpointCont : Cont left right endpoint :=
    surface.right.right.right.right.left
  have scalarLedgerCont : Cont endpoint scalar scalarLedger :=
    surface.right.right.right.right.right.left
  have ledgerCont : Cont scalarLedger additive ledger :=
    surface.right.right.right.right.right.right
  have ledgerAppendEmpty : append scalarLedger additive = BHist.Empty := by
    cases ledgerEmpty
    exact ledgerCont.symm
  have ledgerParts := append_eq_empty_iff.mp ledgerAppendEmpty
  have scalarLedgerAppendEmpty : append endpoint scalar = BHist.Empty := by
    cases ledgerParts.left
    exact scalarLedgerCont.symm
  have scalarLedgerParts := append_eq_empty_iff.mp scalarLedgerAppendEmpty
  have endpointAppendEmpty : append left right = BHist.Empty := by
    cases scalarLedgerParts.left
    exact endpointCont.symm
  have endpointParts := append_eq_empty_iff.mp endpointAppendEmpty
  exact
    And.intro endpointParts.left
      (And.intro endpointParts.right
        (And.intro scalarLedgerParts.right ledgerParts.right))

end BEDC.Derived.BilinFormUp
