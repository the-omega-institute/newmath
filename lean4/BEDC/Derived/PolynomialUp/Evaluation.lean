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
  have zeroXs : PolynomialZeroRemainder xs :=
    PolynomialZeroRemainder_singleton_classifier_self classifiedXs
  have zeroYs : PolynomialZeroRemainder ys :=
    PolynomialZeroRemainder_singleton_classifier_self classifiedYs
  have rawAddZero : PolynomialZeroRemainder (PolynomialSingletonRawAdd xs ys) := by
    clear classifiedXs classifiedYs
    induction zeroXs generalizing ys with
    | nil =>
        induction zeroYs with
        | nil =>
            exact PolynomialZeroRemainder.nil
        | cons headEmpty _tailZero tailRaw =>
            exact PolynomialZeroRemainder.cons
              (append_eq_empty_iff.mpr (And.intro (hsame_refl BHist.Empty) headEmpty))
              tailRaw
    | cons headEmpty _tailZero tailRaw =>
        cases ys with
        | nil =>
            exact PolynomialZeroRemainder.cons
              (append_eq_empty_iff.mpr (And.intro headEmpty (hsame_refl BHist.Empty)))
              (tailRaw PolynomialZeroRemainder.nil)
        | cons y ys =>
            cases zeroYs with
            | cons yEmpty ysZero =>
                exact PolynomialZeroRemainder.cons
                  (append_eq_empty_iff.mpr (And.intro headEmpty yEmpty))
                  (tailRaw ysZero)
  have leftEmpty :
      hsame (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys)) BHist.Empty := by
    have zeroRemainderEvalEmpty :
        forall zs : List BHist, PolynomialZeroRemainder zs ->
          hsame (PolynomialSingletonEval alpha zs) BHist.Empty := by
      intro zs zeroTail
      induction zeroTail with
      | nil =>
          exact hsame_refl BHist.Empty
      | cons headEmpty _tailZero tailEvalEmpty =>
          have productEmpty :
              hsame (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha _))
                BHist.Empty :=
            append_eq_empty_iff.mpr (And.intro carrierAlpha tailEvalEmpty)
          exact append_eq_empty_iff.mpr (And.intro headEmpty productEmpty)
    exact zeroRemainderEvalEmpty (PolynomialSingletonRawAdd xs ys) rawAddZero
  have evalXEmpty : hsame (PolynomialSingletonEval alpha xs) BHist.Empty :=
    (PolynomialSingletonEval_list_classifier_classified carrierAlpha classifiedXs).left.left
  have evalYEmpty : hsame (PolynomialSingletonEval alpha ys) BHist.Empty :=
    (PolynomialSingletonEval_list_classifier_classified carrierAlpha classifiedYs).left.left
  have rightEmpty :
      hsame (append (PolynomialSingletonEval alpha xs) (PolynomialSingletonEval alpha ys))
        BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro evalXEmpty evalYEmpty)
  exact And.intro
    (And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty))))
    (cont_right_unit (PolynomialSingletonEval alpha (PolynomialSingletonRawAdd xs ys)))

end BEDC.Derived.PolynomialUp
