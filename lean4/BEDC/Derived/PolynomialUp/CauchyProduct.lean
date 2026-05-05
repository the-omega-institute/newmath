import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def PolynomialSingletonRawScale (a : BHist) : List BHist -> List BHist
  | [] => []
  | b :: ys => PolynomialSingletonMul a b :: PolynomialSingletonRawScale a ys

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

end BEDC.Derived.PolynomialUp
