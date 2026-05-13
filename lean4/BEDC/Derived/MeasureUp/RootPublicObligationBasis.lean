import BEDC.Derived.MeasureUp

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def MeasureRootPublicObligationBasis (event union value sum endpoint : BHist) : Prop :=
  MeasureZeroBHistClassifier event BHist.Empty ∧ hsame value BHist.Empty ∧
    hsame sum BHist.Empty ∧ hsame union BHist.Empty ∧ Cont value sum endpoint

theorem MeasureRootPublicObligationBasis_event_row_coverage
    {event union value sum endpoint : BHist} :
    MeasureRootPublicObligationBasis event union value sum endpoint ->
      MeasureEventRowCoverage event union value sum endpoint ∧ hsame endpoint BHist.Empty := by
  intro basis
  have coverage :
      MeasureZeroBHistClassifier event BHist.Empty ∧
        MeasureZeroBHistClassifier union BHist.Empty ∧
          MeasureZeroBHistClassifier value sum ∧ MeasureZeroBHistCarrier endpoint :=
    MeasureRootBHist_real_endpoint_threshold basis.left basis.right.left basis.right.right.left
      basis.right.right.right.left basis.right.right.right.right
  exact And.intro coverage coverage.right.right.right

end BEDC.Derived.MeasureUp
