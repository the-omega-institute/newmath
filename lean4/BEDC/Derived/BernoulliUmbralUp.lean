import BEDC.Derived.BernoulliPolynomialUp
import BEDC.Derived.FaulhaberBernoulliUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.BernoulliUmbralUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold
open BEDC.Derived.BernoulliUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat
abbrev RawRatPoly := BEDC.Derived.BernoulliPolynomialUp.RawRatPoly

def rawBernoulliPolynomial (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial n

def rawBernoulliPolynomialShift (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomialShift n

def rawBernoulliPolynomialDifference (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomialDifference n

def rawBernoulliDifferenceRhs (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolynomialUp.rawBernoulliDifferenceRhs n

def rawBernoulliPolynomialDerivative (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomialDerivative n

def rawBernoulliDerivativeRhs (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolynomialUp.rawBernoulliDerivativeRhs n

def umbralBinomialCoeff (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def umbralBernoulliCoeffAt (n k : Nat) : RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawBernoulliPolyCoeffAt n k

inductive UmbralTerm where
  | bernoulli : Nat -> UmbralTerm
  | variablePower : Nat -> UmbralTerm
  | shiftedBernoulliPower : Nat -> UmbralTerm
  | scaledPaddedVariablePower : Nat -> UmbralTerm
  | add : UmbralTerm -> UmbralTerm -> UmbralTerm
  | sub : UmbralTerm -> UmbralTerm -> UmbralTerm
  | scaleNat : Nat -> UmbralTerm -> UmbralTerm
  deriving DecidableEq, Repr

def umbralEval : UmbralTerm -> RawRatPoly
  | .bernoulli n => rawBernoulliPolynomial n
  | .variablePower n =>
      BEDC.Derived.BernoulliPolynomialUp.rawRatPolyPow
        BEDC.Derived.BernoulliPolynomialUp.bernoulliX n
  | .shiftedBernoulliPower n => rawBernoulliPolynomialShift n
  | .scaledPaddedVariablePower n => rawBernoulliDifferenceRhs n
  | .add lhs rhs =>
      BEDC.Derived.BernoulliPolynomialUp.rawRatPolyAdd
        (umbralEval lhs) (umbralEval rhs)
  | .sub lhs rhs =>
      BEDC.Derived.BernoulliPolynomialUp.rawRatPolySub
        (umbralEval lhs) (umbralEval rhs)
  | .scaleNat n body =>
      BEDC.Derived.BernoulliPolynomialUp.rawRatPolyScale
        (BEDC.Derived.BernoulliPolynomialUp.rawRatOfNat n) (umbralEval body)

def umbralBernoulliDeltaTerm (n : Nat) : UmbralTerm :=
  UmbralTerm.sub (UmbralTerm.shiftedBernoulliPower n) (UmbralTerm.bernoulli n)

def umbralBernoulliDeltaRhsTerm : Nat -> UmbralTerm
  | n => UmbralTerm.scaledPaddedVariablePower n

def umbralBernoulliDelta (n : Nat) : RawRatPoly :=
  umbralEval (umbralBernoulliDeltaTerm n)

def umbralBernoulliDeltaRhs (n : Nat) : RawRatPoly :=
  rawBernoulliDifferenceRhs n

def umbralBernoulliRecurrenceRow (n : Nat) : RawRat :=
  rawBernoulliNext (Nat.succ n) (rawBernoulliTable n)

def umbralBernoulliRecurrenceSum (n : Nat) : RawRat :=
  rawBernoulliSum (Nat.succ (Nat.succ n)) (rawBernoulliTable n) 0

def umbralPowerSumFormula (p n : Nat) : RawRat :=
  BEDC.Derived.FaulhaberUp.rawFaulhaberFormula p n

def umbralPowerSumDirect (p n : Nat) : RawRat :=
  BEDC.Derived.FaulhaberUp.rawPowerSum p n

def umbralPowerSumTerms (p n : Nat) : List RawRat :=
  List.map (fun x => BEDC.Derived.FaulhaberUp.rawPowNat x p)
    (BEDC.Derived.FaulhaberUp.powerSumRange 1 n)

def umbralPowerSumFold (p n : Nat) : RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawRatAddMany (umbralPowerSumTerms p n)

def finiteFoldUmbralPowerSum (p n : Nat) : RawRat :=
  umbralPowerSumFold p n

structure BernoulliUmbralExport where
  degree : Nat
  shiftedMinusBase : RawRatPoly
  monomialDelta : RawRatPoly
  derivative : RawRatPoly
  derivativeRhs : RawRatPoly
  recurrenceRow : RawRat

def bernoulliUmbralExport (n : Nat) : BernoulliUmbralExport where
  degree := n
  shiftedMinusBase := umbralBernoulliDelta n
  monomialDelta := umbralBernoulliDeltaRhs n
  derivative := rawBernoulliPolynomialDerivative n
  derivativeRhs := rawBernoulliDerivativeRhs n
  recurrenceRow := umbralBernoulliRecurrenceRow n

def BernoulliPolynomialDifferenceClaim (n : Nat) : Prop :=
  umbralBernoulliDelta n = umbralBernoulliDeltaRhs n

def BernoulliUmbralDifferenceClaim (n : Nat) : Prop :=
  umbralEval (umbralBernoulliDeltaTerm n) =
    umbralEval (umbralBernoulliDeltaRhsTerm n)

def BernoulliPolynomialDerivativeClaim (n : Nat) : Prop :=
  rawBernoulliPolynomialDerivative n = rawBernoulliDerivativeRhs n

def BernoulliPowerSumClaim (p n : Nat) : Prop :=
  umbralPowerSumFormula p n = umbralPowerSumDirect p n

theorem umbralEval_bernoulli (n : Nat) :
    umbralEval (UmbralTerm.bernoulli n) = rawBernoulliPolynomial n := by
  rfl

theorem umbralEval_shiftedBernoulliPower (n : Nat) :
    umbralEval (UmbralTerm.shiftedBernoulliPower n) =
      rawBernoulliPolynomialShift n := by
  rfl

theorem umbralEval_delta (n : Nat) :
    umbralBernoulliDelta n = rawBernoulliPolynomialDifference n := by
  rfl

theorem umbralEval_delta_rhs (n : Nat) :
    umbralEval (umbralBernoulliDeltaRhsTerm n) =
      rawBernoulliDifferenceRhs n := by
  rfl

theorem umbralBinomialCoeff_definition (n k : Nat) :
    umbralBinomialCoeff n k =
      BEDC.Derived.BinomialIdentitiesUp.C n k := by
  rfl

theorem umbralBernoulliCoeffAt_definition (n k : Nat) :
    umbralBernoulliCoeffAt n k =
      match umbralBinomialCoeff n k with
      | 0 => rawZero
      | 1 => rawBernoulli k
      | Nat.succ (Nat.succ c) =>
          rawMulNat (Nat.succ (Nat.succ c)) (rawBernoulli k) := by
  rfl

theorem umbralBinomialCoeff_zero_right (n : Nat) :
    umbralBinomialCoeff n 0 = 1 := by
  exact BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n

theorem umbralBernoulliRecursion (n : Nat) :
    rawBernoulli (Nat.succ n) =
      umbralBernoulliRecurrenceRow n := by
  rfl

theorem umbralBernoulliRecurrenceRow_definition (n : Nat) :
    umbralBernoulliRecurrenceRow n =
      rawNeg
        (rawScaleDen
          (umbralBernoulliRecurrenceSum n)
          (Nat.succ n)) := by
  rfl

theorem umbralPolynomialDifference_zero :
    BernoulliPolynomialDifferenceClaim 0 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_difference_zero

theorem umbralPolynomialDifference_one :
    BernoulliPolynomialDifferenceClaim 1 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_difference_one

theorem umbralPolynomialDifference_two :
    BernoulliPolynomialDifferenceClaim 2 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_difference_two

theorem umbralPolynomialDifference_three :
    BernoulliPolynomialDifferenceClaim 3 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_difference_three

theorem umbralSymbolicDifference_three :
    BernoulliUmbralDifferenceClaim 3 := by
  exact umbralPolynomialDifference_three

theorem umbralPolynomialDifferenceSmallWindow :
    BernoulliPolynomialDifferenceClaim 0 ∧
      BernoulliPolynomialDifferenceClaim 1 ∧
      BernoulliPolynomialDifferenceClaim 2 ∧
      BernoulliPolynomialDifferenceClaim 3 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_difference_small_window

theorem umbralPolynomialDerivative_one :
    BernoulliPolynomialDerivativeClaim 1 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_derivative_one

theorem umbralPolynomialDerivative_two :
    BernoulliPolynomialDerivativeClaim 2 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_derivative_two

theorem umbralPolynomialDerivative_three :
    BernoulliPolynomialDerivativeClaim 3 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_derivative_three

theorem umbralPolynomialDerivativeSmallWindow :
    BernoulliPolynomialDerivativeClaim 1 ∧
      BernoulliPolynomialDerivativeClaim 2 ∧
      BernoulliPolynomialDerivativeClaim 3 := by
  exact BEDC.Derived.BernoulliPolynomialUp.rawBernoulliPolynomial_derivative_small_window

theorem umbralPowerSum_via_bernoulli_polynomial (p n : Nat) :
    umbralPowerSumFormula p n =
      BEDC.Derived.FaulhaberUp.rawFaulhaberFormula p n := by
  rfl

theorem umbralPowerSum_low_order_samples :
    umbralPowerSumFormula 1 3 = umbralPowerSumDirect 1 3 ∧
      umbralPowerSumFormula 2 3 = umbralPowerSumDirect 2 3 ∧
      umbralPowerSumFormula 3 3 = umbralPowerSumDirect 3 3 := by
  exact BEDC.Derived.FaulhaberBernoulliUp.rawFaulhaber_low_order_sample_consistency

theorem umbralPowerSumClaim_low_order_samples :
    BernoulliPowerSumClaim 1 3 ∧
      BernoulliPowerSumClaim 2 3 ∧
      BernoulliPowerSumClaim 3 3 := by
  exact umbralPowerSum_low_order_samples

theorem finiteFold_umbralPowerSumTerms_nil (p : Nat) :
    umbralPowerSumFold p 0 = rawZero := by
  rfl

theorem finiteFoldUmbralPowerSum_definition (p n : Nat) :
    finiteFoldUmbralPowerSum p n =
      BEDC.Derived.BernoulliPolyUp.rawRatAddMany
        (umbralPowerSumTerms p n) := by
  rfl

theorem bernoulliUmbralConstructiveExport :
    BernoulliUmbralDifferenceClaim 3 ∧
      BernoulliPolynomialDerivativeClaim 3 ∧
      umbralPowerSumFormula 3 3 = umbralPowerSumDirect 3 3 ∧
      rawBernoulli 4 = umbralBernoulliRecurrenceRow 3 := by
  exact ⟨umbralSymbolicDifference_three,
    umbralPolynomialDerivative_three,
    (umbralPowerSum_low_order_samples).right.right,
    umbralBernoulliRecursion 3⟩

end BEDC.Derived.BernoulliUmbralUp
