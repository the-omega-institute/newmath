import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealAlgOrderUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem RealAlgOrderConstantCarrier_classifier_obligations {d e d' e' : BHist} :
    RatHistoryCarrier d -> RatHistoryClassifier d e -> hsame d d' -> hsame e e' ->
      RealConstantHistoryCarrier (BHist.e1 d') ∧
        RealConstantHistoryCarrier (BHist.e1 e') ∧
          RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') ∧
            RatHistoryClassifier d' e' := by
  intro carrierD classifiedDE sameD sameE
  have classifiedD'E' : RatHistoryClassifier d' e' :=
    RatHistoryClassifier_hsame_transport sameD sameE classifiedDE
  have carrierD' : RatHistoryCarrier d' :=
    RatHistoryCarrier_hsame_transport sameD carrierD
  have carrierE' : RatHistoryCarrier e' := classifiedD'E'.right.left
  have realCarrierD' : RealConstantHistoryCarrier (BHist.e1 d') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr carrierD'
  have realCarrierE' : RealConstantHistoryCarrier (BHist.e1 e') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr carrierE'
  have realClassifierD'E' : RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedD'E'
  exact And.intro realCarrierD'
    (And.intro realCarrierE'
      (And.intro realClassifierD'E' classifiedD'E'))

end BEDC.Derived.RealAlgOrderUp
