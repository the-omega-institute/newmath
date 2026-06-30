import BEDC.Derived.FaulhaberUp

namespace BEDC.Derived.FaulhaberBernoulliUp

open BEDC.Derived.BernoulliUp
open BEDC.Derived.BernoulliPolyUp
open BEDC.Derived.FaulhaberUp

abbrev RatNum := RationalUp.RatNum

-- 当前 Bernoulli 构造使用 $B_1=-1/2$; 一般式以 Bernoulli 多项式差分为接口。
def rawBernoulliPowerTerm (p j n : Nat) : RawRat :=
  rawFaulhaberTerm p j n

def rawBernoulliPowerTermSum (p n : Nat) : RawRat :=
  rawFaulhaberSumFrom p (p + 2) 0 n

def rawBernoulliPolynomialValue (p n : Nat) : RawRat :=
  rawBernoulliPowerTermSum p n

def rawBernoulliPolynomialDifference (p n : Nat) : RawRat :=
  rawAdd (rawBernoulliPolynomialValue p (n + 1))
    (rawNeg (rawBernoulliPolynomialValue p 1))

def rawFaulhaberBernoulliQuotient (p n : Nat) : RawRat :=
  rawDivNat (rawBernoulliPolynomialDifference p n) p

def faulhaberBernoulliFormula (p n : Nat) : RatNum :=
  rawRatToRat (rawFaulhaberBernoulliQuotient p n)

theorem rawFaulhaberBernoulliTermFormula (p j n : Nat) :
    rawBernoulliPowerTerm p j n =
      rawMul
        (rawBernoulliPolyCoeffAt (p + 1) j)
        (rawOfNat (powNat n (p + 1 - j))) := by
  rfl

theorem rawFaulhaberBernoulliTermSumFormula (p n : Nat) :
    rawBernoulliPowerTermSum p n =
      rawFaulhaberSumFrom p (p + 2) 0 n := by
  rfl

theorem rawFaulhaber_term_sum_matches_polynomial_eval (p n : Nat) :
    rawBernoulliPowerTermSum p n =
      rawFaulhaberBernoulliPolyEval p n := by
  rfl

theorem rawFaulhaberBernoulliPolynomialFormula (p n : Nat) :
    rawFaulhaberBernoulliQuotient p n =
      rawFaulhaberFormula p n := by
  rfl

theorem rawFaulhaberPolynomial_difference_formula (p n : Nat) :
    rawFaulhaberFormula p n =
      rawDivNat
        (rawAdd
          (rawFaulhaberBernoulliPolyEval p (n + 1))
          (rawNeg (rawFaulhaberBernoulliPolyEval p 1)))
        p := by
  rfl

theorem faulhaber_via_bernoulli_polynomial (p n : Nat) :
    RationalUp.RatEq (faulhaberFormula p n)
      (faulhaberBernoulliFormula p n) := by
  exact RationalUp.RatEq_refl _

theorem faulhaber_low_order_scaled_consistency (n : Nat) :
    2 * powerSumNat 1 n = n * (n + 1) ∧
      6 * powerSumNat 2 n = n * (n + 1) * (2 * n + 1) ∧
      4 * powerSumNat 3 n = n * n * (n + 1) * (n + 1) := by
  exact ⟨powerSum_one_closed_scaled n,
    powerSum_two_closed_scaled n,
    powerSum_three_closed_scaled n⟩

theorem rawFaulhaber_low_order_sample_consistency :
    rawFaulhaberFormula 1 3 = rawPowerSum 1 3 ∧
      rawFaulhaberFormula 2 3 = rawPowerSum 2 3 ∧
      rawFaulhaberFormula 3 3 = rawPowerSum 3 3 := by
  exact ⟨rawFaulhaber_small_one,
    rawFaulhaber_small_two,
    rawFaulhaber_small_three⟩

end BEDC.Derived.FaulhaberBernoulliUp
