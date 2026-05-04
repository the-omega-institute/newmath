import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RingSingletonClassifier_cont_result_empty_iff {h k p r : BHist} :
    RingSingletonClassifier h k -> Cont h p r ->
      (hsame r BHist.Empty ↔ RingSingletonCarrier p) := by
  intro classified rel
  constructor
  · intro resultEmpty
    have emptyRel : Cont h p BHist.Empty :=
      cont_result_hsame_transport rel resultEmpty
    exact (cont_empty_result_inversion emptyRel).right
  · intro pEmpty
    exact cont_deterministic rel (by
      cases classified.left
      cases pEmpty
      exact cont_right_unit BHist.Empty)

theorem RingSingletonClassifier_mul_continuation_classifier_iff {x y z r h : BHist} :
    Cont (RingSingletonMul x y) z r ->
      (RingSingletonClassifier r h ↔ RingSingletonCarrier z ∧ RingSingletonCarrier h) := by
  intro continuation
  constructor
  · intro classified
    have emptyContinuation : Cont (RingSingletonMul x y) z BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    exact And.intro (cont_empty_result_inversion emptyContinuation).right classified.right.left
  · intro carriers
    have resultEmpty : RingSingletonCarrier r :=
      cont_deterministic continuation (by
        cases carriers.left
        exact cont_right_unit (RingSingletonMul x y))
    exact And.intro resultEmpty
      (And.intro carriers.right (hsame_trans resultEmpty (hsame_symm carriers.right)))

theorem RingSingletonClassifier_continuation_visible_result_absurd {h k p r : BHist} :
    RingSingletonClassifier h k -> RingSingletonCarrier p ->
      (Cont h p (BHist.e0 r) -> False) ∧ (Cont h p (BHist.e1 r) -> False) := by
  intro classified carrierP
  constructor
  · intro continuation
    have resultEmpty : hsame (BHist.e0 r) BHist.Empty :=
      cont_respects_hsame classified.left carrierP continuation (cont_right_unit BHist.Empty)
    exact not_hsame_e0_empty resultEmpty
  · intro continuation
    have resultEmpty : hsame (BHist.e1 r) BHist.Empty :=
      cont_respects_hsame classified.left carrierP continuation (cont_right_unit BHist.Empty)
    exact not_hsame_e1_empty resultEmpty

end BEDC.Derived.RingUp
