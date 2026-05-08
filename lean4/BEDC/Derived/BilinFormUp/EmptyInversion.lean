import BEDC.Derived.BilinFormUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BilinFormBHistObligationSurface_ledger_empty_inversion
    {left right scalar additive endpoint scalarLedger ledger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame ledger BHist.Empty ->
        hsame left BHist.Empty ∧ hsame right BHist.Empty ∧ hsame scalar BHist.Empty ∧
          hsame additive BHist.Empty := by
  intro surface ledgerEmpty
  have ledgerEmptyCont : Cont scalarLedger additive BHist.Empty :=
    cont_result_hsame_transport surface.right.right.right.right.right.right ledgerEmpty
  have scalarLedgerAdditiveEmpty := cont_empty_result_inversion ledgerEmptyCont
  have scalarLedgerEmpty : hsame scalarLedger BHist.Empty :=
    scalarLedgerAdditiveEmpty.left
  have additiveEmpty : hsame additive BHist.Empty :=
    scalarLedgerAdditiveEmpty.right
  have scalarLedgerEmptyCont : Cont endpoint scalar BHist.Empty :=
    cont_result_hsame_transport surface.right.right.right.right.right.left scalarLedgerEmpty
  have endpointScalarEmpty := cont_empty_result_inversion scalarLedgerEmptyCont
  have endpointEmpty : hsame endpoint BHist.Empty :=
    endpointScalarEmpty.left
  have scalarEmpty : hsame scalar BHist.Empty :=
    endpointScalarEmpty.right
  have endpointEmptyCont : Cont left right BHist.Empty :=
    cont_result_hsame_transport surface.right.right.right.right.left endpointEmpty
  have leftRightEmpty := cont_empty_result_inversion endpointEmptyCont
  exact And.intro leftRightEmpty.left
    (And.intro leftRightEmpty.right
      (And.intro scalarEmpty additiveEmpty))

end BEDC.Derived.BilinFormUp
