import BEDC.Derived.BilinFormUp

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BilinFormBHistObligationSurface_endpoint_empty_inversion
    {left right scalar additive endpoint scalarLedger ledger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame ledger BHist.Empty ->
        hsame left BHist.Empty ∧ hsame right BHist.Empty ∧ hsame scalar BHist.Empty ∧
          hsame additive BHist.Empty := by
  intro surface ledgerEmpty
  have ledgerCont : Cont scalarLedger additive ledger :=
    surface.right.right.right.right.right.right
  have ledgerEmptyCont : Cont scalarLedger additive BHist.Empty :=
    cont_result_hsame_transport ledgerCont ledgerEmpty
  have ledgerParts := cont_empty_result_inversion ledgerEmptyCont
  have scalarLedgerCont : Cont endpoint scalar scalarLedger :=
    surface.right.right.right.right.right.left
  have scalarLedgerEmptyCont : Cont endpoint scalar BHist.Empty :=
    cont_result_hsame_transport scalarLedgerCont ledgerParts.left
  have scalarLedgerParts := cont_empty_result_inversion scalarLedgerEmptyCont
  have endpointCont : Cont left right endpoint :=
    surface.right.right.right.right.left
  have endpointEmptyCont : Cont left right BHist.Empty :=
    cont_result_hsame_transport endpointCont scalarLedgerParts.left
  have endpointParts := cont_empty_result_inversion endpointEmptyCont
  exact And.intro endpointParts.left
    (And.intro endpointParts.right
      (And.intro scalarLedgerParts.right ledgerParts.right))

end BEDC.Derived.BilinFormUp
