import BEDC.Derived.BernoulliPolyUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.PochhammerUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.LaguerrePolynomialUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat
abbrev RawRatPoly := List RawRat
abbrev RatNum := BEDC.Derived.RationalUp.RatNum

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

def rawNormalize : RawRat -> RawRat :=
  BEDC.Derived.BernoulliUp.rawNormalize

def rawMulNat : Nat -> RawRat -> RawRat :=
  BEDC.Derived.BernoulliUp.rawMulNat

def rawRatToRat : RawRat -> RatNum :=
  BEDC.Derived.BernoulliUp.rawRatToRat

def C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def factorial (n : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount n

def rawOfNat (n : Nat) : RawRat :=
  rawMulNat n rawOne

def rawSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)

def rawRatPow : RawRat -> Nat -> RawRat
  | _x, 0 => rawOne
  | x, Nat.succ n => rawMul x (rawRatPow x n)

def rawDivByNat (x : RawRat) : Nat -> RawRat
  | 0 => rawZero
  | Nat.succ n =>
      rawNormalize
        { num := x.num
          denMinusOne := x.den * Nat.succ n - 1 }

def rawLaguerreSign : Nat -> Int
  | 0 => 1
  | Nat.succ k => -rawLaguerreSign k

def rawLaguerreCoeff (n k : Nat) : RawRat :=
  rawNormalize
    { num := rawLaguerreSign k * Int.ofNat (C n k)
      denMinusOne := factorial k - 1 }

def rawLaguerreCoeffsFrom (n fuel k : Nat) : RawRatPoly :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      rawLaguerreCoeff n k ::
        rawLaguerreCoeffsFrom n fuel' (Nat.succ k)

def rawLaguerrePolynomialExplicit (n : Nat) : RawRatPoly :=
  rawLaguerreCoeffsFrom n (Nat.succ n) 0

def laguerrePolynomialExplicit (n : Nat) : List RatNum :=
  (rawLaguerrePolynomialExplicit n).map rawRatToRat

def rawRatListSum : List RawRat -> RawRat
  | [] => rawZero
  | x :: xs => rawAdd x (rawRatListSum xs)

def rawLaguerreTerm (n k : Nat) (x : RawRat) : RawRat :=
  rawMul (rawLaguerreCoeff n k) (rawRatPow x k)

def rawLaguerreTermListFrom (n fuel k : Nat) (x : RawRat) : List RawRat :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      rawLaguerreTerm n k x ::
        rawLaguerreTermListFrom n fuel' (Nat.succ k) x

def rawLaguerreExplicitSum (n : Nat) (x : RawRat) : RawRat :=
  rawRatListSum (rawLaguerreTermListFrom n (Nat.succ n) 0 x)

def rawRatPolyEval (x : RawRat) : RawRatPoly -> RawRat
  | [] => rawZero
  | a :: rest =>
      if x = rawZero then a else rawAdd a (rawMul x (rawRatPolyEval x rest))

def rawLaguerreExplicitAtZero (n : Nat) : RawRat :=
  rawRatPolyEval rawZero (rawLaguerrePolynomialExplicit n)

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
  | b :: p => rawMul a b :: rawRatPolyScale a p

def rawRatPolyShift : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawZero :: a :: p

def rawRatPolyDivByNat (p : RawRatPoly) (n : Nat) : RawRatPoly :=
  p.map (fun x => rawDivByNat x n)

def rawLaguerreRecurrenceRhs (n : Nat) (previous current : RawRatPoly) :
    RawRatPoly :=
  rawRatPolySub
    (rawRatPolySub
      (rawRatPolyScale (rawOfNat (2 * n + 1)) current)
      (rawRatPolyShift current))
    (rawRatPolyScale (rawOfNat n) previous)

def rawLaguerreRecPair : Nat -> RawRatPoly × RawRatPoly
  | 0 =>
      ([rawOne], [rawOne, rawNeg rawOne])
  | Nat.succ n =>
      let pair := rawLaguerreRecPair n
      (pair.2,
        rawRatPolyDivByNat
          (rawLaguerreRecurrenceRhs (Nat.succ n) pair.1 pair.2)
          (Nat.succ (Nat.succ n)))

def rawLaguerrePolynomialRec : Nat -> RawRatPoly
  | 0 => [rawOne]
  | Nat.succ n => (rawLaguerreRecPair n).2

def laguerrePolynomialRec (n : Nat) : List RatNum :=
  (rawLaguerrePolynomialRec n).map rawRatToRat

theorem rawLaguerreCoeff_zero (n : Nat) :
    rawLaguerreCoeff n 0 = rawOne := by
  unfold rawLaguerreCoeff C factorial rawOne rawNormalize
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
  rw [BEDC.Derived.PochhammerUp.natFactorialCount_zero]
  rfl

theorem rawLaguerrePolynomialExplicitAtZero_one (n : Nat) :
    rawLaguerreExplicitAtZero n = rawOne := by
  unfold rawLaguerreExplicitAtZero rawLaguerrePolynomialExplicit
    rawLaguerreCoeffsFrom
  change
    (if rawZero = rawZero then rawLaguerreCoeff n 0 else
      rawAdd (rawLaguerreCoeff n 0)
        (rawMul rawZero
          (rawRatPolyEval rawZero
            (rawLaguerreCoeffsFrom n n 1)))) = rawOne
  rw [if_pos rfl]
  exact rawLaguerreCoeff_zero n

theorem rawLaguerrePolynomialRec_zero :
    rawLaguerrePolynomialRec 0 = [rawOne] := by
  rfl

theorem rawLaguerrePolynomialRec_one :
    rawLaguerrePolynomialRec 1 = [rawOne, rawNeg rawOne] := by
  rfl

private theorem rawLaguerreRecPair_first (n : Nat) :
    (rawLaguerreRecPair n).1 = rawLaguerrePolynomialRec n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

private theorem rawLaguerreRecPair_second (n : Nat) :
    (rawLaguerreRecPair n).2 = rawLaguerrePolynomialRec (Nat.succ n) := by
  rfl

private theorem rawLaguerrePolynomialRec_succ_succ_unfold (n : Nat) :
    rawLaguerrePolynomialRec (Nat.succ (Nat.succ n)) =
      rawRatPolyDivByNat
        (rawLaguerreRecurrenceRhs
          (Nat.succ n)
          (rawLaguerreRecPair n).1
          (rawLaguerreRecPair n).2)
        (Nat.succ (Nat.succ n)) := by
  rfl

theorem rawLaguerrePolynomialRec_three_term (n : Nat) :
    rawRatPolyDivByNat
        (rawLaguerreRecurrenceRhs
          (Nat.succ n)
          (rawLaguerrePolynomialRec n)
          (rawLaguerrePolynomialRec (Nat.succ n)))
        (Nat.succ (Nat.succ n)) =
      rawLaguerrePolynomialRec (Nat.succ (Nat.succ n)) := by
  rw [← rawLaguerreRecPair_first n]
  rw [← rawLaguerreRecPair_second n]
  exact (rawLaguerrePolynomialRec_succ_succ_unfold n).symm

def rawMinusOne : RawRat :=
  rawNeg rawOne

def rawMinusTwo : RawRat :=
  rawNeg (rawOfNat 2)

def rawMinusThree : RawRat :=
  rawNeg (rawOfNat 3)

def rawHalf : RawRat :=
  rawNormalize { num := 1, denMinusOne := 1 }

def rawThreeHalves : RawRat :=
  rawNormalize { num := 3, denMinusOne := 1 }

def rawMinusSixth : RawRat :=
  rawNormalize { num := -1, denMinusOne := 5 }

theorem rawLaguerrePolynomialExplicit_zero :
    rawLaguerrePolynomialExplicit 0 = [rawOne] := by
  rfl

theorem rawLaguerrePolynomialExplicit_one :
    rawLaguerrePolynomialExplicit 1 = [rawOne, rawMinusOne] := by
  rfl

theorem rawLaguerrePolynomialExplicit_two :
    rawLaguerrePolynomialExplicit 2 = [rawOne, rawMinusTwo, rawHalf] := by
  rfl

theorem rawLaguerrePolynomialExplicit_three :
    rawLaguerrePolynomialExplicit 3 =
      [rawOne, rawMinusThree, rawThreeHalves, rawMinusSixth] := by
  rfl

end BEDC.Derived.LaguerrePolynomialUp
