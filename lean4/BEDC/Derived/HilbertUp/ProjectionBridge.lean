import BEDC.Derived.HilbertUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.MetricUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist

theorem HilbertSingletonProjection_standard_bridge {h : BHist} :
    VecSpaceSingletonCarrier h ->
      VecSpaceSingletonClassifier (HilbertSingletonProjection h) h ∧
        MetricDistanceWitness h (HilbertSingletonProjection h) BHist.Empty ∧
          RealConstantHistoryClassifier
            (HilbertSingletonInnerProduct h (HilbertSingletonProjection h))
            (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierH
  have existenceRows := HilbertSingletonProjection_existence carrierH
  have projectionCarrier : VecSpaceSingletonCarrier (HilbertSingletonProjection h) :=
    existenceRows.right.left
  have endpointRows := HilbertSingleton_endpoint_readback carrierH projectionCarrier
  have innerRows :=
    HilbertSingleton_universal_orthogonality carrierH projectionCarrier
  have classifiedProjectionH :
      VecSpaceSingletonClassifier (HilbertSingletonProjection h) h :=
    And.intro projectionCarrier
      (And.intro carrierH (hsame_trans projectionCarrier (hsame_symm carrierH)))
  exact And.intro classifiedProjectionH
    (And.intro endpointRows.right.right innerRows)

end BEDC.Derived.HilbertUp
