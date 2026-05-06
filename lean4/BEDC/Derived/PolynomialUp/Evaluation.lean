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

theorem PolynomialSingletonEval_rawAdd_classified {alpha : BHist} {xs ys : List BHist} :
    PolynomialSingletonCarrier alpha ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
          PolynomialSingletonClassifier
            (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys))
            (append (PolynomialSingletonEval alpha xs) (PolynomialSingletonEval alpha ys)) ∧
          Cont (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys)) BHist.Empty
            (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys)) := by
  intro carrierAlpha classifiedXs classifiedYs
  have rawAddClassified :
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
        (PolynomialSingletonRawAdd xs ys) (PolynomialSingletonRawAdd xs ys) := by
    induction xs generalizing ys with
    | nil =>
        induction ys with
        | nil =>
            constructor
        | cons y ys ih =>
            cases classifiedYs with
            | intro headClassified tailClassified =>
                exact And.intro
                  (And.intro
                    (append_eq_empty_iff.mpr
                      (And.intro (hsame_refl BHist.Empty) headClassified.left))
                    (And.intro
                      (append_eq_empty_iff.mpr
                        (And.intro (hsame_refl BHist.Empty) headClassified.left))
                      (hsame_refl (append BHist.Empty y))))
                  (ih tailClassified)
    | cons x xs ih =>
        cases classifiedXs with
        | intro headXClassified tailXClassified =>
            cases ys with
            | nil =>
                have nilClassified :
                    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier [] [] := by
                  constructor
                exact And.intro
                  (And.intro
                    (append_eq_empty_iff.mpr
                      (And.intro headXClassified.left (hsame_refl BHist.Empty)))
                    (And.intro
                      (append_eq_empty_iff.mpr
                        (And.intro headXClassified.left (hsame_refl BHist.Empty)))
                      (hsame_refl (append x BHist.Empty))))
                  (ih tailXClassified nilClassified)
            | cons y ys =>
                cases classifiedYs with
                | intro headYClassified tailYClassified =>
                    exact And.intro
                      (And.intro
                        (append_eq_empty_iff.mpr
                          (And.intro headXClassified.left headYClassified.left))
                        (And.intro
                          (append_eq_empty_iff.mpr
                            (And.intro headXClassified.left headYClassified.left))
                          (hsame_refl (append x y))))
                      (ih tailXClassified tailYClassified)
  have leftEmpty :
      hsame (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys)) BHist.Empty :=
    (PolynomialSingletonEval_list_classifier_classified carrierAlpha rawAddClassified).left.left
  have evalXsEmpty : hsame (PolynomialSingletonEval alpha xs) BHist.Empty :=
    (PolynomialSingletonEval_list_classifier_classified carrierAlpha classifiedXs).left.left
  have evalYsEmpty : hsame (PolynomialSingletonEval alpha ys) BHist.Empty :=
    (PolynomialSingletonEval_list_classifier_classified carrierAlpha classifiedYs).left.left
  have rightEmpty :
      hsame (append (PolynomialSingletonEval alpha xs) (PolynomialSingletonEval alpha ys))
        BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro evalXsEmpty evalYsEmpty)
  exact And.intro
    (And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty))))
    (cont_right_unit (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys)))

end BEDC.Derived.PolynomialUp
