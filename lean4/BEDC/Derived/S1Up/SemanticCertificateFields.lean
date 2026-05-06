import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem SOne_semantic_name_certificate_fields :
    (∀ {x y e p : BHist}, SOneHistoryCarrier x y e p ->
      SOneProductHistoryCarrier p ∧ hsame e SOneUnitHistory ∧
        ∃ dx dy : BHist, hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
          hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y p) ∧
    (∀ {x y e p x' y' e' p' : BHist},
      SOneComponentClassifier x y e p x' y' e' p' -> hsame e e' ∧ hsame p p') ∧
    (∀ {x y e p equation' : BHist}, SOneHistoryCarrier x y e p -> hsame e equation' ->
      SOneHistoryCarrier x y equation' p) ∧
    (∀ {x y e p x' y' e' p' : BHist}, SOneHistoryCarrier x y e p -> hsame x x' ->
      hsame y y' -> hsame e e' -> hsame p p' -> SOneHistoryCarrier x' y' e' p') ∧
    (∀ {x y e p x' y' e' p' : BHist}, SOneHistoryCarrier x y e p -> hsame x x' ->
      hsame y y' -> hsame e e' -> hsame p p' ->
        SOneProductHistoryCarrier p' ∧ hsame e' SOneUnitHistory ∧
          ∃ dx dy : BHist, hsame x' (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
            hsame y' (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x' y' p') := by
  constructor
  · intro x y e p carrier
    exact SOneHistoryCarrier_public_readback carrier
  · constructor
    · intro x y e p x' y' e' p' classifier
      exact SOneHistoryCarrier_component_classifier_ledger_determinacy classifier.left
        classifier.right.left classifier.right.right.left classifier.right.right.right
    · constructor
      · intro x y e p equation' carrier sameEquation
        exact SOneHistoryCarrier_equation_witness_transport carrier sameEquation
      · constructor
        · intro x y e p x' y' e' p' carrier sameX sameY sameEquation samePoint
          exact SOneHistoryCarrier_coordinate_transport carrier sameX sameY sameEquation
            samePoint
        · intro x y e p x' y' e' p' carrier sameX sameY sameEquation samePoint
          exact SOneHistoryCarrier_public_readback_transport carrier sameX sameY sameEquation
            samePoint

end BEDC.Derived.S1Up
