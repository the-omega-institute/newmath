import BEDC.Derived.BernoulliPolyUp
import BEDC.Derived.BinomialIdentitiesUp

namespace BEDC.Derived.BernoulliPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.BernoulliUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat
abbrev RawRatPoly := BEDC.Derived.BernoulliPolyUp.RawRatPoly

def rawRatMul : RawRat -> RawRat -> RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawRatMul

def rawRatPow : RawRat -> Nat -> RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawRatPow

def rawRatPolyEval : RawRat -> RawRatPoly -> RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawRatPolyEval

def rawBernoulliPolynomial (n : Nat) : RawRatPoly :=
  BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial n

def rawBernoulliPolynomialCoeff (n degree : Nat) : RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawBernoulliPolyCoeff n degree

def rawBernoulliPowerBasisTerm (n k : Nat) : Nat × RawRat :=
  (n - k, rawMulNat (BEDC.Derived.BinomialIdentitiesUp.C n k) (rawBernoulli k))

def rawBernoulliPowerBasisTermsFrom (n fuel k : Nat) : List (Nat × RawRat) :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      rawBernoulliPowerBasisTerm n k ::
        rawBernoulliPowerBasisTermsFrom n fuel' (Nat.succ k)

def rawBernoulliPowerBasisTerms (n : Nat) : List (Nat × RawRat) :=
  rawBernoulliPowerBasisTermsFrom n (Nat.succ n) 0

def bernoulliPolynomial (n : Nat) : List RationalUp.RatNum :=
  (rawBernoulliPolynomial n).map rawRatToRat

def bernoulliPolynomialUp (n : BHist) : List RationalUp.RatNum :=
  bernoulliPolynomial (bwordLength n)

def rawRatSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)

def rawRatOfNat (n : Nat) : RawRat :=
  rawMulNat n rawOne

def rawRatPolyZero : RawRatPoly :=
  []

def rawRatPolyOne : RawRatPoly :=
  [rawOne]

def rawRatPolyAdd : RawRatPoly -> RawRatPoly -> RawRatPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => rawAdd a b :: rawRatPolyAdd p q

def rawRatPolyNeg : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawNeg a :: rawRatPolyNeg p

def rawRatPolySub (p q : RawRatPoly) : RawRatPoly :=
  rawRatPolyAdd p (rawRatPolyNeg q)

def rawRatPolyScale (a : RawRat) : RawRatPoly -> RawRatPoly
  | [] => []
  | b :: p => rawRatMul a b :: rawRatPolyScale a p

def rawRatPolyShift : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawZero :: a :: p

def rawRatPolyMulLeft (q : RawRatPoly) : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawRatPolyAdd (rawRatPolyScale a q) (rawRatPolyShift (rawRatPolyMulLeft q p))

def rawRatPolyMul (p q : RawRatPoly) : RawRatPoly :=
  rawRatPolyMulLeft q p

def rawRatPolyPow (p : RawRatPoly) : Nat -> RawRatPoly
  | 0 => rawRatPolyOne
  | Nat.succ n => rawRatPolyMul p (rawRatPolyPow p n)

def rawRatPolyComposeWith (q : RawRatPoly) : RawRatPoly -> RawRatPoly
  | [] => rawRatPolyZero
  | a :: rest => rawRatPolyAdd [a] (rawRatPolyMul q (rawRatPolyComposeWith q rest))

def rawRatPolyCompose (p q : RawRatPoly) : RawRatPoly :=
  rawRatPolyComposeWith q p

def rawRatPolyDerivFrom : Nat -> RawRatPoly -> RawRatPoly
  | _, [] => []
  | degree, a :: p =>
      rawMulNat degree a :: rawRatPolyDerivFrom (Nat.succ degree) p

def rawRatPolyDeriv : RawRatPoly -> RawRatPoly
  | [] => []
  | _ :: p => rawRatPolyDerivFrom 1 p

def bernoulliX : RawRatPoly :=
  [rawZero, rawOne]

def bernoulliXPlusOne : RawRatPoly :=
  [rawOne, rawOne]

def bernoulliOneMinusX : RawRatPoly :=
  [rawOne, rawNeg rawOne]

def rawBernoulliPolynomialAtZero (n : Nat) : RawRat :=
  rawRatPolyEval rawZero (rawBernoulliPolynomial n)

def rawBernoulliPolynomialAtOne (n : Nat) : RawRat :=
  rawRatPolyEval rawOne (rawBernoulliPolynomial n)

def rawBernoulliPolynomialShift (n : Nat) : RawRatPoly :=
  rawRatPolyCompose (rawBernoulliPolynomial n) bernoulliXPlusOne

def rawBernoulliPolynomialOneMinusX (n : Nat) : RawRatPoly :=
  rawRatPolyCompose (rawBernoulliPolynomial n) bernoulliOneMinusX

def rawBernoulliPolynomialDifference (n : Nat) : RawRatPoly :=
  rawRatPolySub (rawBernoulliPolynomialShift n) (rawBernoulliPolynomial n)

def rawBernoulliPolynomialDerivative (n : Nat) : RawRatPoly :=
  rawRatPolyDeriv (rawBernoulliPolynomial n)

def rawBernoulliDerivativeRhs (n : Nat) : RawRatPoly :=
  rawRatPolyScale (rawRatOfNat n) (rawBernoulliPolynomial (n - 1))

inductive NatParity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace NatParity

def flip : NatParity -> NatParity
  | even => odd
  | odd => even

theorem flip_flip (p : NatParity) :
    flip (flip p) = p := by
  cases p <;> rfl

end NatParity

def natParity : Nat -> NatParity
  | 0 => NatParity.even
  | Nat.succ n => NatParity.flip (natParity n)

def paritySign (p : NatParity) (x : RawRat) : RawRat :=
  match p with
  | NatParity.even => x
  | NatParity.odd => rawNeg x

def rawBernoulliSymmetryRhs (n : Nat) : RawRatPoly :=
  rawRatPolyScale (paritySign (natParity n) rawOne) (rawBernoulliPolynomial n)

def rawRatPolyZeros : Nat -> RawRatPoly
  | 0 => []
  | Nat.succ n => rawZero :: rawRatPolyZeros n

def rawBernoulliDifferenceRhs (n : Nat) : RawRatPoly :=
  match n with
  | 0 => [rawZero]
  | Nat.succ m => rawRatPolyZeros m ++ [rawRatOfNat (Nat.succ m), rawZero]

def BernoulliPolynomialDifferenceClaim (n : Nat) : Prop :=
  rawBernoulliPolynomialDifference n = rawBernoulliDifferenceRhs n

def BernoulliPolynomialSymmetryClaim (n : Nat) : Prop :=
  rawBernoulliPolynomialOneMinusX n = rawBernoulliSymmetryRhs n

def BernoulliPolynomialDerivativeClaim (n : Nat) : Prop :=
  rawBernoulliPolynomialDerivative n = rawBernoulliDerivativeRhs n

structure BernoulliPolynomialExport where
  degree : Nat
  coefficients : RawRatPoly
  powerBasisTerms : List (Nat × RawRat)
  valueAtZero : RawRat
  shiftedDifference : RawRatPoly
  symmetryReadback : RawRatPoly
  derivativeReadback : RawRatPoly
  deriving DecidableEq, Repr

def bernoulliPolynomialExport (n : Nat) : BernoulliPolynomialExport where
  degree := n
  coefficients := rawBernoulliPolynomial n
  powerBasisTerms := rawBernoulliPowerBasisTerms n
  valueAtZero := rawBernoulliPolynomialAtZero n
  shiftedDifference := rawBernoulliPolynomialDifference n
  symmetryReadback := rawBernoulliPolynomialOneMinusX n
  derivativeReadback := rawBernoulliPolynomialDerivative n

theorem rawBernoulliPolynomial_definition (n : Nat) :
    rawBernoulliPolynomial n =
      BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial n := by
  rfl

theorem rawBernoulliPolynomial_coeff_formula (n degree : Nat) :
    rawBernoulliPolynomialCoeff n degree =
      match BEDC.Derived.BinomialIdentitiesUp.C n (n - degree) with
      | 0 => rawZero
      | 1 => rawBernoulli (n - degree)
      | Nat.succ (Nat.succ c) =>
          rawMulNat (Nat.succ (Nat.succ c)) (rawBernoulli (n - degree)) := by
  rfl

theorem rawBernoulliPowerBasisTerm_formula (n k : Nat) :
    rawBernoulliPowerBasisTerm n k =
      (n - k,
        rawMulNat (BEDC.Derived.BinomialIdentitiesUp.C n k)
          (rawBernoulli k)) := by
  rfl

theorem rawBernoulliPowerBasisTerms_definition (n : Nat) :
    rawBernoulliPowerBasisTerms n =
      rawBernoulliPowerBasisTermsFrom n (Nat.succ n) 0 := by
  rfl

theorem bernoulliPolynomialExport_coefficients (n : Nat) :
    (bernoulliPolynomialExport n).coefficients =
      rawBernoulliPolynomial n := by
  rfl

theorem bernoulliPolynomialExport_valueAtZero (n : Nat) :
    (bernoulliPolynomialExport n).valueAtZero = rawBernoulli n := by
  exact BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial_eval_zero n

theorem bernoulliPolynomial_definition (n : Nat) :
    bernoulliPolynomial n =
      (rawBernoulliPolynomial n).map rawRatToRat := by
  rfl

theorem bernoulliPolynomialUp_unary_result (n : BHist) :
    bernoulliPolynomialUp n = bernoulliPolynomial (bwordLength n) := by
  rfl

theorem rawBernoulliPolynomial_eval_zero (n : Nat) :
    rawBernoulliPolynomialAtZero n = rawBernoulli n := by
  exact BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial_eval_zero n

theorem bernoulliPolynomial_constant_value (n : Nat) :
    (bernoulliPolynomial n).head? = some (bernoulli n) := by
  exact BEDC.Derived.BernoulliPolyUp.bernoulliPolynomial_constant_value n

theorem rawBernoulliPolynomial_zero :
    rawBernoulliPolynomial 0 = [rawOne] := by
  exact BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial_zero

theorem rawBernoulliPolynomial_one :
    rawBernoulliPolynomial 1 = [rawBernoulli 1, rawBernoulli 0] := by
  exact BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial_one

theorem rawBernoulliPolynomial_two :
    rawBernoulliPolynomial 2 =
      [rawBernoulli 2, rawMulNat 2 (rawBernoulli 1), rawBernoulli 0] := by
  rfl

theorem rawBernoulliPolynomial_three :
    rawBernoulliPolynomial 3 =
      [rawBernoulli 3, rawMulNat 3 (rawBernoulli 2),
        rawMulNat 3 (rawBernoulli 1), rawBernoulli 0] := by
  rfl

theorem rawBernoulliPolynomial_four :
    rawBernoulliPolynomial 4 =
      [rawBernoulli 4, rawMulNat 4 (rawBernoulli 3),
        rawMulNat 6 (rawBernoulli 2), rawMulNat 4 (rawBernoulli 1),
        rawBernoulli 0] := by
  rfl

theorem rawBernoulliPolynomial_derivative_one :
    rawBernoulliPolynomialDerivative 1 = rawBernoulliDerivativeRhs 1 := by
  rfl

theorem rawBernoulliPolynomial_derivative_two :
    rawBernoulliPolynomialDerivative 2 = rawBernoulliDerivativeRhs 2 := by
  rfl

theorem rawBernoulliPolynomial_derivative_three :
    rawBernoulliPolynomialDerivative 3 = rawBernoulliDerivativeRhs 3 := by
  rfl

theorem rawBernoulliPolynomial_derivative_four :
    rawBernoulliPolynomialDerivative 4 = rawBernoulliDerivativeRhs 4 := by
  decide

theorem rawBernoulliPolynomial_derivative_five :
    rawBernoulliPolynomialDerivative 5 = rawBernoulliDerivativeRhs 5 := by
  decide

theorem rawBernoulliPolynomial_difference_zero :
    rawBernoulliPolynomialDifference 0 = rawBernoulliDifferenceRhs 0 := by
  rfl

theorem rawBernoulliPolynomial_difference_one :
    rawBernoulliPolynomialDifference 1 = rawBernoulliDifferenceRhs 1 := by
  rfl

theorem rawBernoulliPolynomial_difference_two :
    rawBernoulliPolynomialDifference 2 = rawBernoulliDifferenceRhs 2 := by
  rfl

theorem rawBernoulliPolynomial_difference_three :
    rawBernoulliPolynomialDifference 3 = rawBernoulliDifferenceRhs 3 := by
  rfl

theorem rawBernoulliPolynomial_difference_four :
    rawBernoulliPolynomialDifference 4 = rawBernoulliDifferenceRhs 4 := by
  decide

theorem rawBernoulliPolynomial_difference_five :
    rawBernoulliPolynomialDifference 5 = rawBernoulliDifferenceRhs 5 := by
  decide

theorem rawBernoulliPolynomial_symmetry_zero :
    rawBernoulliPolynomialOneMinusX 0 = rawBernoulliSymmetryRhs 0 := by
  rfl

theorem rawBernoulliPolynomial_symmetry_one :
    rawBernoulliPolynomialOneMinusX 1 = rawBernoulliSymmetryRhs 1 := by
  rfl

theorem rawBernoulliPolynomial_symmetry_two :
    rawBernoulliPolynomialOneMinusX 2 = rawBernoulliSymmetryRhs 2 := by
  rfl

theorem rawBernoulliPolynomial_symmetry_three :
    rawBernoulliPolynomialOneMinusX 3 = rawBernoulliSymmetryRhs 3 := by
  rfl

theorem rawBernoulliPolynomial_symmetry_four :
    rawBernoulliPolynomialOneMinusX 4 = rawBernoulliSymmetryRhs 4 := by
  decide

theorem rawBernoulliPolynomial_symmetry_five :
    rawBernoulliPolynomialOneMinusX 5 = rawBernoulliSymmetryRhs 5 := by
  decide

theorem rawBernoulliPolynomial_difference_small_window :
    rawBernoulliPolynomialDifference 0 = rawBernoulliDifferenceRhs 0 ∧
      rawBernoulliPolynomialDifference 1 = rawBernoulliDifferenceRhs 1 ∧
      rawBernoulliPolynomialDifference 2 = rawBernoulliDifferenceRhs 2 ∧
      rawBernoulliPolynomialDifference 3 = rawBernoulliDifferenceRhs 3 := by
  exact ⟨rawBernoulliPolynomial_difference_zero,
    rawBernoulliPolynomial_difference_one,
    rawBernoulliPolynomial_difference_two,
    rawBernoulliPolynomial_difference_three⟩

theorem rawBernoulliPolynomial_difference_verified_window :
    BernoulliPolynomialDifferenceClaim 0 ∧
      BernoulliPolynomialDifferenceClaim 1 ∧
      BernoulliPolynomialDifferenceClaim 2 ∧
      BernoulliPolynomialDifferenceClaim 3 ∧
      BernoulliPolynomialDifferenceClaim 4 ∧
      BernoulliPolynomialDifferenceClaim 5 := by
  exact ⟨rawBernoulliPolynomial_difference_zero,
    rawBernoulliPolynomial_difference_one,
    rawBernoulliPolynomial_difference_two,
    rawBernoulliPolynomial_difference_three,
    rawBernoulliPolynomial_difference_four,
    rawBernoulliPolynomial_difference_five⟩

theorem rawBernoulliPolynomial_symmetry_small_window :
    rawBernoulliPolynomialOneMinusX 0 = rawBernoulliSymmetryRhs 0 ∧
      rawBernoulliPolynomialOneMinusX 1 = rawBernoulliSymmetryRhs 1 ∧
      rawBernoulliPolynomialOneMinusX 2 = rawBernoulliSymmetryRhs 2 ∧
      rawBernoulliPolynomialOneMinusX 3 = rawBernoulliSymmetryRhs 3 := by
  exact ⟨rawBernoulliPolynomial_symmetry_zero,
    rawBernoulliPolynomial_symmetry_one,
    rawBernoulliPolynomial_symmetry_two,
    rawBernoulliPolynomial_symmetry_three⟩

theorem rawBernoulliPolynomial_symmetry_verified_window :
    BernoulliPolynomialSymmetryClaim 0 ∧
      BernoulliPolynomialSymmetryClaim 1 ∧
      BernoulliPolynomialSymmetryClaim 2 ∧
      BernoulliPolynomialSymmetryClaim 3 ∧
      BernoulliPolynomialSymmetryClaim 4 ∧
      BernoulliPolynomialSymmetryClaim 5 := by
  exact ⟨rawBernoulliPolynomial_symmetry_zero,
    rawBernoulliPolynomial_symmetry_one,
    rawBernoulliPolynomial_symmetry_two,
    rawBernoulliPolynomial_symmetry_three,
    rawBernoulliPolynomial_symmetry_four,
    rawBernoulliPolynomial_symmetry_five⟩

theorem rawBernoulliPolynomial_derivative_small_window :
    rawBernoulliPolynomialDerivative 1 = rawBernoulliDerivativeRhs 1 ∧
      rawBernoulliPolynomialDerivative 2 = rawBernoulliDerivativeRhs 2 ∧
      rawBernoulliPolynomialDerivative 3 = rawBernoulliDerivativeRhs 3 := by
  exact ⟨rawBernoulliPolynomial_derivative_one,
    rawBernoulliPolynomial_derivative_two,
    rawBernoulliPolynomial_derivative_three⟩

theorem rawBernoulliPolynomial_derivative_verified_window :
    BernoulliPolynomialDerivativeClaim 1 ∧
      BernoulliPolynomialDerivativeClaim 2 ∧
      BernoulliPolynomialDerivativeClaim 3 ∧
      BernoulliPolynomialDerivativeClaim 4 ∧
      BernoulliPolynomialDerivativeClaim 5 := by
  exact ⟨rawBernoulliPolynomial_derivative_one,
    rawBernoulliPolynomial_derivative_two,
    rawBernoulliPolynomial_derivative_three,
    rawBernoulliPolynomial_derivative_four,
    rawBernoulliPolynomial_derivative_five⟩

theorem bernoulliPolynomial_constructive_export :
    rawBernoulliPolynomialAtZero 4 = rawBernoulli 4 ∧
      rawBernoulliPolynomialDifference 3 = rawBernoulliDifferenceRhs 3 ∧
      rawBernoulliPolynomialOneMinusX 3 = rawBernoulliSymmetryRhs 3 ∧
      rawBernoulliPolynomialDerivative 3 = rawBernoulliDerivativeRhs 3 := by
  exact ⟨rawBernoulliPolynomial_eval_zero 4,
    rawBernoulliPolynomial_difference_three,
    rawBernoulliPolynomial_symmetry_three,
    rawBernoulliPolynomial_derivative_three⟩

theorem bernoulliPolynomial_window_export :
    rawBernoulliPolynomialAtZero 5 = rawBernoulli 5 ∧
      BernoulliPolynomialDifferenceClaim 5 ∧
      BernoulliPolynomialSymmetryClaim 5 ∧
      BernoulliPolynomialDerivativeClaim 5 := by
  exact ⟨rawBernoulliPolynomial_eval_zero 5,
    rawBernoulliPolynomial_difference_five,
    rawBernoulliPolynomial_symmetry_five,
    rawBernoulliPolynomial_derivative_five⟩

end BEDC.Derived.BernoulliPolynomialUp
