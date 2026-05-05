import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem PolynomialZeroRemainder_singleton_classifier_self {t : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier t t ->
      PolynomialZeroRemainder t := by
  intro classified
  induction t with
  | nil =>
      exact PolynomialZeroRemainder.nil
  | cons x xs ih =>
      cases classified with
      | intro headClassified tailClassified =>
          exact PolynomialZeroRemainder.cons headClassified.left (ih tailClassified)

theorem PolynomialSingletonEval_zero_constant_term {a : BHist} {t : List BHist} :
    PolynomialSingletonCarrier a ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier t t ->
        PolynomialSingletonClassifier (PolynomialSingletonEval BHist.Empty (a :: t)) a := by
  intro carrierA classifiedTail
  exact PolynomialSingletonEval_zero_cons_constant carrierA
    (PolynomialZeroRemainder_singleton_classifier_self classifiedTail)

theorem PolynomialSingletonEval_coefficient_shift {alpha : BHist} {xs : List BHist} :
    PolynomialSingletonCarrier alpha ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
        PolynomialSingletonClassifier
          (PolynomialSingletonEval alpha (BHist.Empty :: xs))
          (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs)) ∧
        Cont (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs)) BHist.Empty
          (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs)) := by
  intro carrierAlpha classified
  have evalRows :=
    PolynomialSingletonEval_list_classifier_classified carrierAlpha classified
  have alphaClassified : PolynomialSingletonClassifier alpha alpha :=
    And.intro carrierAlpha (And.intro carrierAlpha (hsame_refl alpha))
  have shiftedEvalClassified :
      PolynomialSingletonClassifier
        (PolynomialSingletonEval alpha (BHist.Empty :: xs))
        (append BHist.Empty
          (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs))) :=
    PolynomialSingletonClassifier_continuation_closed
      (And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
      (PolynomialSingletonClassifier_continuation_closed alphaClassified evalRows.left
        (cont_intro rfl) (cont_intro rfl))
      (cont_intro rfl) (cont_intro rfl)
  have shiftedTargetClassified :
      PolynomialSingletonClassifier
        (PolynomialSingletonEval alpha (BHist.Empty :: xs))
        (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs)) :=
    have targetCarrier :
        PolynomialSingletonCarrier
          (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs)) :=
      append_eq_empty_iff.mpr (And.intro carrierAlpha evalRows.left.left)
    And.intro shiftedEvalClassified.left
      (And.intro targetCarrier (hsame_trans shiftedEvalClassified.left (hsame_symm targetCarrier)))
  exact And.intro shiftedTargetClassified
    (cont_right_unit (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha xs)))

end BEDC.Derived.PolynomialUp
