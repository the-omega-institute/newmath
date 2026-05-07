import BEDC.Derived.HilbertUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.BanachUp
open BEDC.Derived.MetricUp
open BEDC.Derived.NormUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist

theorem HilbertSingleton_ledger_exhaustion {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      VecSpaceSingletonClassifier m BHist.Empty /\
        BanachSingletonCarrier m /\
          MetricDistanceWitness m n BHist.Empty /\
            RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
              (BHist.e1 (BHist.e1 BHist.Empty)) /\
              RealConstantHistoryClassifier (NormSingletonNorm m)
                (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierM carrierN
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have classifiedM : VecSpaceSingletonClassifier m BHist.Empty :=
    And.intro carrierM (And.intro emptyCarrier carrierM)
  have distance :
      MetricDistanceWitness m n BHist.Empty :=
    MetricDistanceWitness_empty_distance_iff.mpr (And.intro carrierM carrierN)
  have banachCarrier : BanachSingletonCarrier m :=
    And.intro carrierM
      (MetricDistanceWitness_empty_distance_iff.mpr
        (And.intro carrierM (hsame_refl BHist.Empty)))
  have innerConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    HilbertSingleton_universal_orthogonality carrierM carrierN
  have endpointRows := HilbertSingleton_endpoint_readback carrierM carrierN
  exact And.intro classifiedM
    (And.intro banachCarrier
      (And.intro distance
        (And.intro innerConstant endpointRows.left)))

end BEDC.Derived.HilbertUp
