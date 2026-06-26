import BEDC.Derived.BernoulliUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.BernoulliPolyUp

open BEDC.Derived.BernoulliUp

abbrev RawRatPoly : Type := List RawRat

def rawRatEq (x y : RawRat) : Prop :=
  x = y

def rawRatMul (x y : RawRat) : RawRat :=
  rawNormalize
    { num := x.num * y.num
      denMinusOne := x.den * y.den - 1 }

def rawRatPow : RawRat -> Nat -> RawRat
  | _x, 0 => rawOne
  | x, Nat.succ n => rawRatMul x (rawRatPow x n)

def rawRatAddMany : List RawRat -> RawRat
  | [] => rawZero
  | x :: xs => rawAdd x (rawRatAddMany xs)

def rawRatPolyEval (x : RawRat) : RawRatPoly -> RawRat
  | [] => rawZero
  | a :: rest =>
      if x = rawZero then a else rawAdd a (rawRatMul x (rawRatPolyEval x rest))

def rawBernoulliPolyCoeffAt (n k : Nat) : RawRat :=
  match binomNat n k with
  | 0 => rawZero
  | 1 => rawBernoulli k
  | Nat.succ (Nat.succ c) => rawMulNat (Nat.succ (Nat.succ c)) (rawBernoulli k)

def rawBernoulliPolyCoeff (n degree : Nat) : RawRat :=
  rawBernoulliPolyCoeffAt n (n - degree)

def rawBernoulliPolyCoeffsFrom (n fuel k : Nat) : RawRatPoly :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      rawBernoulliPolyCoeff n k ::
        rawBernoulliPolyCoeffsFrom n fuel' (Nat.succ k)

def rawBernoulliPolynomial (n : Nat) : RawRatPoly :=
  rawBernoulliPolyCoeffsFrom n (Nat.succ n) 0

def bernoulliPolynomial (n : Nat) : List RationalUp.RatNum :=
  (rawBernoulliPolynomial n).map rawRatToRat

def bernoulliPolynomialUp (n : FKernel.Hist.BHist) : List RationalUp.RatNum :=
  bernoulliPolynomial (FKernel.ExternalBinary.bwordLength n)

theorem binomNat_self (n : Nat) :
    binomNat n n = 1 := by
  unfold binomNat
  rw [BEDC.Derived.FactorialUp.natChooseFn_boundary_self]
  rfl

theorem rawBernoulliPolyCoeff_zero_degree (n : Nat) :
    rawBernoulliPolyCoeff n 0 = rawBernoulli n := by
  unfold rawBernoulliPolyCoeff rawBernoulliPolyCoeffAt
  rw [Nat.sub_zero]
  rw [binomNat_self n]

theorem rawBernoulliPolynomial_constant_coeff (n : Nat) :
    (rawBernoulliPolynomial n).head? = some (rawBernoulli n) := by
  unfold rawBernoulliPolynomial rawBernoulliPolyCoeffsFrom
  exact congrArg some (rawBernoulliPolyCoeff_zero_degree n)

theorem rawBernoulliPolynomial_eval_zero (n : Nat) :
    rawRatPolyEval rawZero (rawBernoulliPolynomial n) = rawBernoulli n := by
  unfold rawRatPolyEval rawBernoulliPolynomial rawBernoulliPolyCoeffsFrom
  exact rawBernoulliPolyCoeff_zero_degree n

theorem rawBernoulliPolynomial_zero :
  rawBernoulliPolynomial 0 = [rawOne] := by
  unfold rawBernoulliPolynomial rawBernoulliPolyCoeffsFrom
  rw [rawBernoulliPolyCoeff_zero_degree 0]
  rw [rawBernoulli_zero_value]
  rfl

theorem bernoulliPolynomial_zero :
    bernoulliPolynomial 0 = [rawRatToRat rawOne] := by
  unfold bernoulliPolynomial
  rw [rawBernoulliPolynomial_zero]
  rfl

theorem bernoulliPolynomial_constant_value (n : Nat) :
    (bernoulliPolynomial n).head? = some (bernoulli n) := by
  unfold bernoulliPolynomial bernoulli
  rw [List.head?_map]
  rw [rawBernoulliPolynomial_constant_coeff n]
  rfl

theorem rawBernoulliPolynomial_one :
    rawBernoulliPolynomial 1 =
      [rawBernoulli 1, rawBernoulli 0] := by
  rfl

theorem rawBernoulliPolynomial_one_at_zero :
    rawRatPolyEval rawZero (rawBernoulliPolynomial 1) = rawBernoulli 1 := by
  rfl

theorem rawBernoulliPolynomial_one_difference_at_zero :
    rawAdd
        (rawRatPolyEval rawOne (rawBernoulliPolynomial 1))
        (rawNeg (rawRatPolyEval rawZero (rawBernoulliPolynomial 1))) =
      rawOne := by
  rfl

theorem rawBernoulliPolynomial_small_values :
    rawBernoulliPolynomial 0 = [rawOne] ∧
      rawRatPolyEval rawZero (rawBernoulliPolynomial 1) = rawBernoulli 1 ∧
      rawAdd
          (rawRatPolyEval rawOne (rawBernoulliPolynomial 1))
          (rawNeg (rawRatPolyEval rawZero (rawBernoulliPolynomial 1))) =
        rawOne := by
  exact ⟨rawBernoulliPolynomial_zero,
    rawBernoulliPolynomial_one_at_zero,
    rawBernoulliPolynomial_one_difference_at_zero⟩

end BEDC.Derived.BernoulliPolyUp
