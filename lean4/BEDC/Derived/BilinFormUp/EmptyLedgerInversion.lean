import BEDC.Derived.BilinFormUp

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BilinFormBHistObligationSurface_empty_ledger_inversion
    {left right scalar additive endpoint scalarLedger ledger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame ledger BHist.Empty ->
        hsame left BHist.Empty ∧ hsame right BHist.Empty ∧ hsame scalar BHist.Empty ∧
          hsame additive BHist.Empty := by
  intro surface ledgerEmpty
  have ledgerCont : Cont scalarLedger additive ledger :=
    surface.right.right.right.right.right.right
  have emptyLedgerCont : Cont scalarLedger additive BHist.Empty :=
    cont_result_hsame_transport ledgerCont ledgerEmpty
  have ledgerParts := cont_empty_result_inversion emptyLedgerCont
  have scalarLedgerEmpty : hsame scalarLedger BHist.Empty := ledgerParts.left
  have additiveEmpty : hsame additive BHist.Empty := ledgerParts.right
  have scalarLedgerCont : Cont endpoint scalar scalarLedger :=
    surface.right.right.right.right.right.left
  have emptyScalarLedgerCont : Cont endpoint scalar BHist.Empty :=
    cont_result_hsame_transport scalarLedgerCont scalarLedgerEmpty
  have scalarLedgerParts := cont_empty_result_inversion emptyScalarLedgerCont
  have endpointEmpty : hsame endpoint BHist.Empty := scalarLedgerParts.left
  have scalarEmpty : hsame scalar BHist.Empty := scalarLedgerParts.right
  have endpointCont : Cont left right endpoint :=
    surface.right.right.right.right.left
  have emptyEndpointCont : Cont left right BHist.Empty :=
    cont_result_hsame_transport endpointCont endpointEmpty
  have endpointParts := cont_empty_result_inversion emptyEndpointCont
  exact And.intro endpointParts.left
    (And.intro endpointParts.right
      (And.intro scalarEmpty additiveEmpty))

end BEDC.Derived.BilinFormUp
