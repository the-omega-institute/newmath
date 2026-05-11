import BEDC.Derived.MeasureUp

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem MeasureProbabilityNormalizationRow {event union value sum endpoint total : BHist} :
    MeasureZeroBHistClassifier event BHist.Empty -> hsame value BHist.Empty ->
      hsame sum BHist.Empty -> hsame union BHist.Empty -> Cont value sum endpoint ->
        hsame total BHist.Empty ->
          MeasureZeroBHistClassifier event BHist.Empty ∧
            MeasureZeroBHistClassifier union BHist.Empty ∧
              MeasureZeroBHistCarrier endpoint ∧ MeasureZeroBHistCarrier total := by
  intro eventClassified valueZero sumZero unionZero endpointRow totalZero
  have rootRows :
      MeasureZeroBHistClassifier event BHist.Empty ∧
        MeasureZeroBHistClassifier union BHist.Empty ∧
          MeasureZeroBHistClassifier value sum ∧ MeasureZeroBHistCarrier endpoint :=
    MeasureRootBHist_real_endpoint_threshold eventClassified valueZero sumZero unionZero
      endpointRow
  exact And.intro rootRows.left
    (And.intro rootRows.right.left (And.intro rootRows.right.right.right totalZero))

end BEDC.Derived.MeasureUp
