import BEDC.Derived.FaulhaberBernoulliUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.FaulhaberPolynomialUp

open BEDC.Derived.BernoulliUp
open BEDC.Derived.BernoulliPolyUp
open BEDC.Derived.FaulhaberUp
open BEDC.Derived.FaulhaberBernoulliUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat

def oneToNPowerTerms (p n : Nat) : List Nat :=
  powerSumRange p n

def oneToNPowerSum (p n : Nat) : Nat :=
  sumNatList (oneToNPowerTerms p n)

theorem oneToNPowerSum_matches_recursive_sum (p n : Nat) :
    oneToNPowerSum p n = powerSumNat p n := by
  exact powerSumRange_sum p n

def rawRatListSum : List RawRat -> RawRat
  | [] => rawZero
  | x :: xs => rawAdd x (rawRatListSum xs)

def bernoulliPowerTerm (p j x : Nat) : RawRat :=
  rawFaulhaberTerm p j x

def bernoulliPowerTermListFrom (p fuel j x : Nat) : List RawRat :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      bernoulliPowerTerm p j x ::
        bernoulliPowerTermListFrom p fuel' (Nat.succ j) x

def bernoulliPowerTermList (p x : Nat) : List RawRat :=
  bernoulliPowerTermListFrom p (p + 2) 0 x

theorem rawRatListSum_bernoulliPowerTermListFrom
    (p fuel j x : Nat) :
    rawRatListSum (bernoulliPowerTermListFrom p fuel j x) =
      rawFaulhaberSumFrom p fuel j x := by
  induction fuel generalizing j with
  | zero =>
      rfl
  | succ fuel ih =>
      change rawAdd (bernoulliPowerTerm p j x)
          (rawRatListSum
            (bernoulliPowerTermListFrom p fuel (Nat.succ j) x)) =
        rawAdd (rawFaulhaberTerm p j x)
          (rawFaulhaberSumFrom p fuel (Nat.succ j) x)
      rw [ih (Nat.succ j)]
      rfl

def bernoulliPolynomialValueFromTerms (p x : Nat) : RawRat :=
  rawRatListSum (bernoulliPowerTermList p x)

theorem bernoulliPolynomialValueFromTerms_matches_eval
    (p x : Nat) :
    bernoulliPolynomialValueFromTerms p x =
      rawFaulhaberBernoulliPolyEval p x := by
  exact rawRatListSum_bernoulliPowerTermListFrom p (p + 2) 0 x

def rawFaulhaberPolynomial (p n : Nat) : RawRat :=
  rawDivNat
    (rawAdd
      (bernoulliPolynomialValueFromTerms p (n + 1))
      (rawNeg (bernoulliPolynomialValueFromTerms p 1)))
    p

def faulhaberPolynomial (p n : Nat) : RationalUp.RatNum :=
  rawRatToRat (rawFaulhaberPolynomial p n)

theorem rawFaulhaberPolynomial_general_bernoulli_formula
    (p n : Nat) :
    rawFaulhaberPolynomial p n =
      rawDivNat
        (rawAdd
          (rawRatListSum (bernoulliPowerTermList p (n + 1)))
          (rawNeg (rawRatListSum (bernoulliPowerTermList p 1))))
        p := by
  rfl

theorem rawFaulhaberPolynomial_matches_existing_formula
    (p n : Nat) :
    rawFaulhaberPolynomial p n = rawFaulhaberFormula p n := by
  unfold rawFaulhaberPolynomial
  rw [bernoulliPolynomialValueFromTerms_matches_eval p (n + 1)]
  rw [bernoulliPolynomialValueFromTerms_matches_eval p 1]
  rfl

theorem faulhaberPolynomial_via_bernoulli_formula
    (p n : Nat) :
    RationalUp.RatEq (faulhaberPolynomial p n)
      (faulhaberBernoulliFormula p n) := by
  unfold faulhaberPolynomial
  rw [rawFaulhaberPolynomial_matches_existing_formula p n]
  exact faulhaber_via_bernoulli_polynomial p n

def triangularClosedNumerator (n : Nat) : Nat :=
  n * (n + 1)

def squareClosedNumerator (n : Nat) : Nat :=
  n * (n + 1) * (2 * n + 1)

def cubeClosedNumerator (n : Nat) : Nat :=
  n * n * (n + 1) * (n + 1)

theorem powerSum_one_triangular_closed_scaled (n : Nat) :
    2 * powerSumNat 1 n = triangularClosedNumerator n := by
  exact powerSum_one_closed_scaled n

theorem powerSum_two_square_closed_scaled (n : Nat) :
    6 * powerSumNat 2 n = squareClosedNumerator n := by
  exact powerSum_two_closed_scaled n

theorem powerSum_three_cube_closed_scaled (n : Nat) :
    4 * powerSumNat 3 n = cubeClosedNumerator n := by
  exact powerSum_three_closed_scaled n

private theorem natMulAssocPure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem natPairSquareShuffle (a b : Nat) :
    a * a * b * b = (a * b) * (a * b) := by
  calc
    a * a * b * b = (a * (a * b)) * b := by
      exact congrArg (fun x => x * b) (natMulAssocPure a a b)
    _ = (a * (b * a)) * b := by
      exact congrArg (fun x => (a * x) * b) (Nat.mul_comm a b)
    _ = ((a * b) * a) * b := by
      exact congrArg (fun x => x * b) (natMulAssocPure a b a).symm
    _ = (a * b) * (a * b) := by
      exact natMulAssocPure (a * b) a b

theorem powerSum_three_square_of_triangular_scaled (n : Nat) :
    4 * powerSumNat 3 n =
      (2 * powerSumNat 1 n) * (2 * powerSumNat 1 n) := by
  calc
    4 * powerSumNat 3 n = cubeClosedNumerator n :=
      powerSum_three_cube_closed_scaled n
    _ = (n * (n + 1)) * (n * (n + 1)) :=
      natPairSquareShuffle n (n + 1)
    _ = (2 * powerSumNat 1 n) * (2 * powerSumNat 1 n) := by
      rw [powerSum_one_closed_scaled n]

theorem faulhaberPolynomial_low_order_closed_scaled (n : Nat) :
    2 * powerSumNat 1 n = triangularClosedNumerator n ∧
      6 * powerSumNat 2 n = squareClosedNumerator n ∧
      4 * powerSumNat 3 n = cubeClosedNumerator n ∧
      4 * powerSumNat 3 n =
        (2 * powerSumNat 1 n) * (2 * powerSumNat 1 n) := by
  exact ⟨powerSum_one_triangular_closed_scaled n,
    powerSum_two_square_closed_scaled n,
    powerSum_three_cube_closed_scaled n,
    powerSum_three_square_of_triangular_scaled n⟩

end BEDC.Derived.FaulhaberPolynomialUp
