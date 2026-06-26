import BEDC.Derived.BernoulliPolyUp
import BEDC.Derived.BinomialIdentitiesUp

namespace BEDC.Derived.EulerPolyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat
abbrev RawRatPoly := BEDC.Derived.BernoulliPolyUp.RawRatPoly

def rawZero : RawRat :=
  BEDC.Derived.BernoulliUp.rawZero

def rawOne : RawRat :=
  BEDC.Derived.BernoulliUp.rawOne

def rawNeg : RawRat -> RawRat :=
  BEDC.Derived.BernoulliUp.rawNeg

def rawAdd : RawRat -> RawRat -> RawRat :=
  BEDC.Derived.BernoulliUp.rawAdd

def rawMul : RawRat -> RawRat -> RawRat :=
  BEDC.Derived.BernoulliPolyUp.rawRatMul

def rawMulNat : Nat -> RawRat -> RawRat :=
  BEDC.Derived.BernoulliUp.rawMulNat

def rawScaleDen : RawRat -> Nat -> RawRat :=
  BEDC.Derived.BernoulliUp.rawScaleDen

def rawSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)

def rawOfNat (n : Nat) : RawRat :=
  rawMulNat n rawOne

def rawTwo : RawRat :=
  rawOfNat 2

def rawHalf : RawRat :=
  rawScaleDen rawOne 1

def rawRatPow : RawRat -> Nat -> RawRat
  | _x, 0 => rawOne
  | x, Nat.succ n => rawMul x (rawRatPow x n)

def ratPolyZero : RawRatPoly :=
  []

def ratPolyOne : RawRatPoly :=
  [rawOne]

def ratPolyAdd : RawRatPoly -> RawRatPoly -> RawRatPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => rawAdd a b :: ratPolyAdd p q

def ratPolyNeg : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawNeg a :: ratPolyNeg p

def ratPolySub (p q : RawRatPoly) : RawRatPoly :=
  ratPolyAdd p (ratPolyNeg q)

def ratPolyScale (a : RawRat) : RawRatPoly -> RawRatPoly
  | [] => []
  | b :: p => rawMul a b :: ratPolyScale a p

def ratPolyShift : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawZero :: a :: p

def ratPolyMulLeft (q : RawRatPoly) : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => ratPolyAdd (ratPolyScale a q) (ratPolyShift (ratPolyMulLeft q p))

def ratPolyMul (p q : RawRatPoly) : RawRatPoly :=
  ratPolyMulLeft q p

def ratPolyPow (p : RawRatPoly) : Nat -> RawRatPoly
  | 0 => ratPolyOne
  | Nat.succ n => ratPolyMul p (ratPolyPow p n)

def ratPolyEval (x : RawRat) : RawRatPoly -> RawRat
  | [] => rawZero
  | a :: p => rawAdd a (rawMul x (ratPolyEval x p))

def ratPolyComposeWith (q : RawRatPoly) : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: rest => ratPolyAdd [a] (ratPolyMul q (ratPolyComposeWith q rest))

def ratPolyCompose (p q : RawRatPoly) : RawRatPoly :=
  ratPolyComposeWith q p

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

def predTwo : Nat -> Nat
  | 0 => 0
  | Nat.succ 0 => Nat.succ 0
  | Nat.succ (Nat.succ n) => n

theorem natParity_predTwo (n : Nat) :
    natParity (predTwo n) = natParity n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          change natParity n = NatParity.flip (NatParity.flip (natParity n))
          exact (NatParity.flip_flip (natParity n)).symm

def paritySign (p : NatParity) (x : RawRat) : RawRat :=
  match p with
  | NatParity.even => x
  | NatParity.odd => rawNeg x

def halfFloor : Nat -> Nat
  | 0 => 0
  | Nat.succ 0 => 0
  | Nat.succ (Nat.succ n) => Nat.succ (halfFloor n)

def powTwo : Nat -> Nat
  | 0 => 1
  | Nat.succ n => 2 * powTwo n

def rawDivByPowTwo (x : RawRat) (n : Nat) : RawRat :=
  rawScaleDen x (powTwo n - 1)

def rawEulerEvenSum (row : Nat) : List RawRat -> Nat -> RawRat
  | [], _k => rawZero
  | e :: es, k =>
      rawAdd
        (rawMulNat (BEDC.Derived.BernoulliUp.binomNat (2 * row) (2 * k)) e)
        (rawEulerEvenSum row es (Nat.succ k))

def rawEulerEvenNext (row : Nat) (previous : List RawRat) : RawRat :=
  rawNeg (rawEulerEvenSum row previous 0)

def rawEulerEvenTable : Nat -> List RawRat × RawRat
  | 0 => ([rawOne], rawOne)
  | Nat.succ row =>
      let previous := rawEulerEvenTable row
      let next := rawEulerEvenNext (Nat.succ row) previous.1
      (previous.1 ++ [next], next)

def rawEulerEven (m : Nat) : RawRat :=
  (rawEulerEvenTable m).2

def rawEulerNumberByIndex (n : Nat) : RawRat :=
  match natParity n with
  | NatParity.even => rawEulerEven (halfFloor n)
  | NatParity.odd => rawZero

structure CenteredTerm where
  coeff : RawRat
  exponent : Nat
  deriving DecidableEq, Repr

abbrev CenteredRatPoly := List CenteredTerm

def rawEulerCenteredCoeff (n m : Nat) : RawRat :=
  rawDivByPowTwo
    (rawMulNat (BEDC.Derived.BernoulliUp.binomNat n (2 * m)) (rawEulerEven m))
    (2 * m)

def rawEulerCenteredTermsFrom (n exponent fuel m : Nat) : CenteredRatPoly :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      { coeff := rawEulerCenteredCoeff n m, exponent := exponent } ::
        rawEulerCenteredTermsFrom n (predTwo exponent) fuel' (Nat.succ m)

def rawEulerPolynomial (n : Nat) : CenteredRatPoly :=
  rawEulerCenteredTermsFrom n n (Nat.succ (halfFloor n)) 0

def eulerPolynomial (n : Nat) : CenteredRatPoly :=
  rawEulerPolynomial n

def centeredMirror : CenteredRatPoly -> CenteredRatPoly
  | [] => []
  | t :: ts =>
      { coeff := paritySign (natParity t.exponent) t.coeff, exponent := t.exponent } ::
        centeredMirror ts

def centeredSigned (p : NatParity) : CenteredRatPoly -> CenteredRatPoly
  | [] => []
  | t :: ts =>
      { coeff := paritySign p t.coeff, exponent := t.exponent } ::
        centeredSigned p ts

theorem centeredMirror_termsFrom (n exponent fuel m : Nat) :
    centeredMirror (rawEulerCenteredTermsFrom n exponent fuel m) =
      centeredSigned (natParity exponent) (rawEulerCenteredTermsFrom n exponent fuel m) := by
  induction fuel generalizing exponent m with
  | zero =>
      rfl
  | succ fuel ih =>
      change
        { coeff := paritySign (natParity exponent) (rawEulerCenteredCoeff n m),
          exponent := exponent } ::
          centeredMirror
            (rawEulerCenteredTermsFrom n (predTwo exponent) fuel (Nat.succ m)) =
        { coeff := paritySign (natParity exponent) (rawEulerCenteredCoeff n m),
          exponent := exponent } ::
          centeredSigned (natParity exponent)
            (rawEulerCenteredTermsFrom n (predTwo exponent) fuel (Nat.succ m))
      have tail :=
        ih (predTwo exponent) (Nat.succ m)
      rw [tail]
      rw [natParity_predTwo exponent]

theorem eulerPolynomial_centered_symmetry (n : Nat) :
    centeredMirror (eulerPolynomial n) =
      centeredSigned (natParity n) (eulerPolynomial n) := by
  unfold eulerPolynomial rawEulerPolynomial
  exact centeredMirror_termsFrom n n (Nat.succ (halfFloor n)) 0

def eulerPolynomialOneMinusX (n : Nat) : CenteredRatPoly :=
  centeredMirror (eulerPolynomial n)

def eulerPolynomialParitySigned (n : Nat) : CenteredRatPoly :=
  centeredSigned (natParity n) (eulerPolynomial n)

theorem eulerPolynomial_oneMinusX_symmetry (n : Nat) :
    eulerPolynomialOneMinusX n = eulerPolynomialParitySigned n := by
  exact eulerPolynomial_centered_symmetry n

def centeredTermEval (u : RawRat) (t : CenteredTerm) : RawRat :=
  rawMul t.coeff (rawRatPow u t.exponent)

def centeredEval (u : RawRat) : CenteredRatPoly -> RawRat
  | [] => rawZero
  | t :: ts => rawAdd (centeredTermEval u t) (centeredEval u ts)

def centeredUnitPowerBasis : RawRatPoly :=
  [rawNeg rawHalf, rawOne]

def centeredTermToPowerBasis (t : CenteredTerm) : RawRatPoly :=
  ratPolyScale t.coeff (ratPolyPow centeredUnitPowerBasis t.exponent)

def centeredToPowerBasis : CenteredRatPoly -> RawRatPoly
  | [] => ratPolyZero
  | t :: ts => ratPolyAdd (centeredTermToPowerBasis t) (centeredToPowerBasis ts)

def eulerPolynomialPowerBasis (n : Nat) : RawRatPoly :=
  centeredToPowerBasis (eulerPolynomial n)

def eulerPolynomialRat (n : Nat) : List BEDC.Derived.RationalUp.RatNum :=
  (eulerPolynomialPowerBasis n).map BEDC.Derived.BernoulliUp.rawRatToRat

def eulerPolynomialUp (n : BHist) : List BEDC.Derived.RationalUp.RatNum :=
  eulerPolynomialRat (bwordLength n)

def eulerNumber (n : Nat) : RawRat :=
  rawMul (rawOfNat (powTwo n)) (centeredEval rawZero (eulerPolynomial n))

def eulerNumberUp (n : BHist) : BEDC.Derived.RationalUp.RatNum :=
  BEDC.Derived.BernoulliUp.rawRatToRat (eulerNumber (bwordLength n))

theorem eulerNumber_half_scaled_value (n : Nat) :
    rawMul (rawOfNat (powTwo n)) (centeredEval rawZero (eulerPolynomial n)) =
      eulerNumber n := by
  rfl

theorem eulerNumber_zero_value :
    eulerNumber 0 = rawOne := by
  rfl

theorem eulerNumber_one_value :
    eulerNumber 1 = rawZero := by
  rfl

def bernoulliHalfArgument : RawRatPoly :=
  [rawZero, rawHalf]

def eulerBernoulliRelationRhs (n : Nat) : RawRatPoly :=
  let degree := Nat.succ n
  let bernoulli := BEDC.Derived.BernoulliPolyUp.rawBernoulliPolynomial degree
  let halfBernoulli :=
    ratPolyCompose bernoulli bernoulliHalfArgument
  let scaledHalf := ratPolyScale (rawOfNat (powTwo degree)) halfBernoulli
  ratPolyScale (rawScaleDen rawTwo n) (ratPolySub bernoulli scaledHalf)

theorem rawEulerEven_zero :
    rawEulerEven 0 = rawOne := by
  rfl

theorem rawEulerNumber_zero :
    rawEulerNumberByIndex 0 = rawOne := by
  rfl

theorem rawEulerNumber_one :
    rawEulerNumberByIndex 1 = rawZero := by
  rfl

theorem eulerPolynomial_zero :
    eulerPolynomial 0 = [{ coeff := rawOne, exponent := 0 }] := by
  rfl

theorem eulerPolynomial_one :
    eulerPolynomial 1 = [{ coeff := rawOne, exponent := 1 }] := by
  rfl

theorem eulerPolynomial_zero_symmetry :
    centeredMirror (eulerPolynomial 0) =
      centeredSigned (natParity 0) (eulerPolynomial 0) := by
  exact eulerPolynomial_centered_symmetry 0

theorem eulerPolynomial_one_symmetry :
    centeredMirror (eulerPolynomial 1) =
      centeredSigned (natParity 1) (eulerPolynomial 1) := by
  exact eulerPolynomial_centered_symmetry 1

end BEDC.Derived.EulerPolyUp
