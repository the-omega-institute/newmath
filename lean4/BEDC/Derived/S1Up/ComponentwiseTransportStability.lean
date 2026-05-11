import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist

theorem SOneStandardBridgeComponentwiseTransport_stability {x y e p x' y' e' p' : BHist} :
    SOneComponentClassifier x y e p x' y' e' p' ->
      SOneHistoryCarrier x y e p ->
        SOneHistoryCarrier x' y' e' p' ->
          hsame e e' ∧ hsame p p' ∧ SOneComponentClassifier x y e p x' y' e' p' := by
  intro classifier sourceCarrier targetCarrier
  have ledger :=
    SOneHistoryCarrier_component_classifier_ledger_determinacy sourceCarrier targetCarrier
      classifier.right.right.left classifier.right.right.right
  exact And.intro ledger.left (And.intro ledger.right classifier)

end BEDC.Derived.S1Up
