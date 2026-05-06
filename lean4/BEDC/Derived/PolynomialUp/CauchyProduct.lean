import BEDC.Derived.PolynomialUp.Evaluation

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def PolynomialSingletonRawMul : List BHist -> List BHist -> List BHist
  | [], _ => []
  | a :: xs, ys =>
      PolynomialSingletonRawAdd (PolynomialSingletonRawScale a ys)
        (BHist.Empty :: PolynomialSingletonRawMul xs ys)

theorem PolynomialSingletonRawScale_zero_remainder
    {a : BHist} {ys : List BHist} :
    PolynomialSingletonCarrier a -> PolynomialZeroRemainder ys ->
      PolynomialZeroRemainder (PolynomialSingletonRawScale a ys) := by
  intro carrierA zeroTail
  induction zeroTail with
  | nil =>
      exact PolynomialZeroRemainder.nil
  | cons headEmpty _tailZero tailScaled =>
      exact PolynomialZeroRemainder.cons
        (append_eq_empty_iff.mpr (And.intro carrierA headEmpty)) tailScaled

theorem PolynomialZeroRemainder_eval_empty {alpha : BHist} {ys : List BHist} :
    PolynomialSingletonCarrier alpha -> PolynomialZeroRemainder ys ->
      hsame (PolynomialSingletonEval alpha ys) BHist.Empty := by
  intro carrierAlpha zeroTail
  induction zeroTail with
  | nil =>
      exact hsame_refl BHist.Empty
  | cons headEmpty _tailZero tailEvalEmpty =>
      have productEmpty :
          hsame (PolynomialSingletonMul alpha (PolynomialSingletonEval alpha _)) BHist.Empty :=
        append_eq_empty_iff.mpr (And.intro carrierAlpha tailEvalEmpty)
      exact append_eq_empty_iff.mpr (And.intro headEmpty productEmpty)

theorem PolynomialSingletonEval_raw_scale_empty_classified
    {alpha a : BHist} {ys : List BHist} :
    PolynomialSingletonCarrier alpha -> PolynomialSingletonCarrier a -> PolynomialZeroRemainder ys ->
      hsame (PolynomialSingletonEval alpha (PolynomialSingletonRawScale a ys)) BHist.Empty ∧
        hsame (PolynomialSingletonMul a (PolynomialSingletonEval alpha ys)) BHist.Empty ∧
          PolynomialSingletonClassifier
            (PolynomialSingletonEval alpha (PolynomialSingletonRawScale a ys))
            (PolynomialSingletonMul a (PolynomialSingletonEval alpha ys)) := by
  intro carrierAlpha carrierA zeroTail
  have scaledZero : PolynomialZeroRemainder (PolynomialSingletonRawScale a ys) :=
    PolynomialSingletonRawScale_zero_remainder carrierA zeroTail
  have leftEmpty :
      hsame (PolynomialSingletonEval alpha (PolynomialSingletonRawScale a ys)) BHist.Empty :=
    PolynomialZeroRemainder_eval_empty carrierAlpha scaledZero
  have evalEmpty : hsame (PolynomialSingletonEval alpha ys) BHist.Empty :=
    PolynomialZeroRemainder_eval_empty carrierAlpha zeroTail
  have rightEmpty :
      hsame (PolynomialSingletonMul a (PolynomialSingletonEval alpha ys)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierA evalEmpty)
  exact And.intro leftEmpty
    (And.intro rightEmpty
      (And.intro leftEmpty (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))))

theorem PolynomialSingletonRawAdd_zero_remainder
    {xs ys : List BHist} :
    PolynomialZeroRemainder xs -> PolynomialZeroRemainder ys ->
      PolynomialZeroRemainder (PolynomialSingletonRawAdd xs ys) := by
  intro zeroXs zeroYs
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

theorem PolynomialSingletonRawMul_zero_remainder
    {xs ys : List BHist} :
    PolynomialZeroRemainder xs -> PolynomialZeroRemainder ys ->
      PolynomialZeroRemainder (PolynomialSingletonRawMul xs ys) := by
  intro zeroXs zeroYs
  induction zeroXs with
  | nil =>
      exact PolynomialZeroRemainder.nil
  | cons headEmpty _tailZero tailProductZero =>
      exact PolynomialSingletonRawAdd_zero_remainder
        (PolynomialSingletonRawScale_zero_remainder headEmpty zeroYs)
        (PolynomialZeroRemainder.cons (hsame_refl BHist.Empty) tailProductZero)

theorem PolynomialSingletonEval_rawMul_classified {alpha : BHist} {xs ys : List BHist} :
    PolynomialSingletonCarrier alpha ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
        BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
          PolynomialSingletonClassifier
            (PolynomialSingletonEval alpha (PolynomialSingletonRawMul xs ys))
            (append (PolynomialSingletonEval alpha xs) (PolynomialSingletonEval alpha ys)) := by
  intro carrierAlpha classifiedXs classifiedYs
  have zeroYs : PolynomialZeroRemainder ys :=
    BEDC.Derived.PolynomialUp.PolynomialZeroRemainder_singleton_classifier_self classifiedYs
  induction xs with
  | nil =>
      have evalYsEmpty : hsame (PolynomialSingletonEval alpha ys) BHist.Empty :=
        PolynomialZeroRemainder_eval_empty carrierAlpha zeroYs
      have rightEmpty :
          hsame (append (PolynomialSingletonEval alpha []) (PolynomialSingletonEval alpha ys))
            BHist.Empty :=
        append_eq_empty_iff.mpr (And.intro (hsame_refl BHist.Empty) evalYsEmpty)
      exact And.intro (hsame_refl BHist.Empty)
        (And.intro rightEmpty (hsame_symm rightEmpty))
  | cons x xs ih =>
      cases classifiedXs with
      | intro headClassified tailClassified =>
          have zeroXs : PolynomialZeroRemainder xs :=
            BEDC.Derived.PolynomialUp.PolynomialZeroRemainder_singleton_classifier_self
              tailClassified
          have scaledZero : PolynomialZeroRemainder (PolynomialSingletonRawScale x ys) :=
            PolynomialSingletonRawScale_zero_remainder headClassified.left zeroYs
          have productZero :
              PolynomialZeroRemainder (PolynomialSingletonRawMul xs ys) :=
            PolynomialSingletonRawMul_zero_remainder zeroXs zeroYs
          have rawAddZero :
              PolynomialZeroRemainder
                (PolynomialSingletonRawAdd (PolynomialSingletonRawScale x ys)
                  (BHist.Empty :: PolynomialSingletonRawMul xs ys)) :=
            PolynomialSingletonRawAdd_zero_remainder scaledZero
              (PolynomialZeroRemainder.cons (hsame_refl BHist.Empty) productZero)
          have leftEmpty :
              hsame
                (PolynomialSingletonEval alpha
                  (PolynomialSingletonRawAdd (PolynomialSingletonRawScale x ys)
                    (BHist.Empty :: PolynomialSingletonRawMul xs ys)))
                BHist.Empty :=
            PolynomialZeroRemainder_eval_empty carrierAlpha rawAddZero
          have classifiedCons :
              BEDC.Derived.ListUp.ListClassifierSpec
                PolynomialSingletonClassifier (x :: xs) (x :: xs) :=
            And.intro headClassified tailClassified
          have evalXEmpty : hsame (PolynomialSingletonEval alpha (x :: xs)) BHist.Empty :=
            (PolynomialSingletonEval_list_classifier_classified carrierAlpha
              classifiedCons).left.left
          have evalYEmpty : hsame (PolynomialSingletonEval alpha ys) BHist.Empty :=
            PolynomialZeroRemainder_eval_empty carrierAlpha zeroYs
          have rightEmpty :
              hsame (append (PolynomialSingletonEval alpha (x :: xs))
                  (PolynomialSingletonEval alpha ys)) BHist.Empty :=
            append_eq_empty_iff.mpr (And.intro evalXEmpty evalYEmpty)
          exact And.intro leftEmpty
            (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem PolynomialSingletonRawMul_commutative_classified {xs ys : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier xs xs ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier ys ys ->
        PolynomialSingletonClassifier
            (PolynomialSingletonAddFold (PolynomialSingletonRawMul xs ys)) BHist.Empty ∧
          PolynomialSingletonClassifier
              (PolynomialSingletonAddFold (PolynomialSingletonRawMul ys xs)) BHist.Empty ∧
            hsame (append (PolynomialSingletonAddFold (PolynomialSingletonRawMul xs ys))
                BHist.Empty)
              (append (PolynomialSingletonAddFold (PolynomialSingletonRawMul ys xs))
                BHist.Empty) := by
  intro classifiedXs classifiedYs
  have zeroXs : PolynomialZeroRemainder xs :=
    BEDC.Derived.PolynomialUp.PolynomialZeroRemainder_singleton_classifier_self
      classifiedXs
  have zeroYs : PolynomialZeroRemainder ys :=
    BEDC.Derived.PolynomialUp.PolynomialZeroRemainder_singleton_classifier_self
      classifiedYs
  have productXYZero : PolynomialZeroRemainder (PolynomialSingletonRawMul xs ys) :=
    PolynomialSingletonRawMul_zero_remainder zeroXs zeroYs
  have productYXZero : PolynomialZeroRemainder (PolynomialSingletonRawMul ys xs) :=
    PolynomialSingletonRawMul_zero_remainder zeroYs zeroXs
  have foldXYEmpty :
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawMul xs ys)) BHist.Empty :=
    PolynomialSingletonAddFold_zero_remainder_empty productXYZero
  have foldYXEmpty :
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawMul ys xs)) BHist.Empty :=
    PolynomialSingletonAddFold_zero_remainder_empty productYXZero
  have classifiedXY :
      PolynomialSingletonClassifier
        (PolynomialSingletonAddFold (PolynomialSingletonRawMul xs ys)) BHist.Empty :=
    PolynomialZeroRemainder_addFold_empty_classified productXYZero
  have classifiedYX :
      PolynomialSingletonClassifier
        (PolynomialSingletonAddFold (PolynomialSingletonRawMul ys xs)) BHist.Empty :=
    PolynomialZeroRemainder_addFold_empty_classified productYXZero
  have appendXYEmpty :
      hsame (append (PolynomialSingletonAddFold (PolynomialSingletonRawMul xs ys))
        BHist.Empty) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro foldXYEmpty (hsame_refl BHist.Empty))
  have appendYXEmpty :
      hsame (append (PolynomialSingletonAddFold (PolynomialSingletonRawMul ys xs))
        BHist.Empty) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro foldYXEmpty (hsame_refl BHist.Empty))
  exact And.intro classifiedXY
    (And.intro classifiedYX (hsame_trans appendXYEmpty (hsame_symm appendYXEmpty)))

end BEDC.Derived.PolynomialUp
