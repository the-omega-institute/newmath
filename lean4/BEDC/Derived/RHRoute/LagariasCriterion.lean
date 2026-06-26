import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.HarmonicUp

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.LagariasCriterion

open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.RationalUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat

structure CalcRat where
  num : Int
  den : Nat

def rawDen (x : RawRat) : Nat :=
  x.den

def intAbsNat : Int -> Nat
  | Int.ofNat n => n
  | Int.negSucc n => Nat.succ n

def intLeBool : Int -> Int -> Bool
  | Int.ofNat a, Int.ofNat b => Nat.ble a b
  | Int.negSucc _, Int.ofNat _ => true
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc a, Int.negSucc b => Nat.ble b a

def factorial : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorial n

def calcDen (x : CalcRat) : Nat :=
  match x.den with
  | 0 => 1
  | Nat.succ d => Nat.succ d

def calcNormalize (x : CalcRat) : CalcRat :=
  { num := x.num, den := calcDen x }

def calcOfIntOverNat (num : Int) (den : Nat) : CalcRat :=
  calcNormalize { num := num, den := den }

def calcOfNat (n : Nat) : CalcRat :=
  calcOfIntOverNat (Int.ofNat n) 1

def calcZero : CalcRat :=
  calcOfNat 0

def calcOne : CalcRat :=
  calcOfNat 1

def calcTwo : CalcRat :=
  calcOfNat 2

def calcAdd (x y : CalcRat) : CalcRat :=
  calcNormalize
    { num := x.num * Int.ofNat (calcDen y) + y.num * Int.ofNat (calcDen x)
      den := calcDen x * calcDen y }

def calcNeg (x : CalcRat) : CalcRat :=
  { num := -x.num, den := calcDen x }

def calcSub (x y : CalcRat) : CalcRat :=
  calcAdd x (calcNeg y)

def calcMul (x y : CalcRat) : CalcRat :=
  calcNormalize { num := x.num * y.num, den := calcDen x * calcDen y }

def calcInv (x : CalcRat) : CalcRat :=
  match x.num with
  | Int.ofNat 0 => calcZero
  | Int.ofNat (Nat.succ n) => { num := Int.ofNat (calcDen x), den := Nat.succ n }
  | Int.negSucc n => { num := -Int.ofNat (calcDen x), den := Nat.succ n }

def calcDiv (x y : CalcRat) : CalcRat :=
  calcMul x (calcInv y)

def calcDivByNat (x : CalcRat) (n : Nat) : CalcRat :=
  match n with
  | 0 => calcZero
  | Nat.succ _ => calcNormalize { num := x.num, den := calcDen x * n }

def calcOneOverNat (n : Nat) : CalcRat :=
  calcOfIntOverNat 1 n

def calcHarmonic : Nat -> CalcRat
  | 0 => calcZero
  | Nat.succ n => calcAdd (calcHarmonic n) (calcOneOverNat (Nat.succ n))

def calcPow (x : CalcRat) : Nat -> CalcRat
  | 0 => calcOne
  | Nat.succ n => calcMul x (calcPow x n)

def calcExpSeriesTerm (x : CalcRat) (k : Nat) : CalcRat :=
  calcDivByNat (calcPow x k) (factorial k)

def calcExpPartial (fuel : Nat) (x : CalcRat) : CalcRat :=
  match fuel with
  | 0 => calcExpSeriesTerm x 0
  | Nat.succ n => calcAdd (calcExpPartial n x) (calcExpSeriesTerm x (Nat.succ n))

def calcExpTailBound (fuel : Nat) (x : CalcRat) : CalcRat :=
  calcMul (calcExpSeriesTerm x (Nat.succ fuel))
    (calcOfIntOverNat (Int.ofNat (fuel + 2)) 2)

def calcExpLowerBound (fuel : Nat) (x : CalcRat) : CalcRat :=
  calcExpPartial fuel x

def calcExpUpperBound (fuel : Nat) (x : CalcRat) : CalcRat :=
  calcAdd (calcExpPartial fuel x) (calcExpTailBound fuel x)

def calcLnZ (x : CalcRat) : CalcRat :=
  calcDiv (calcSub x calcOne) (calcAdd x calcOne)

def calcLnOddTerm (z : CalcRat) (k : Nat) : CalcRat :=
  calcMul calcTwo (calcDivByNat (calcPow z (2 * k + 1)) (2 * k + 1))

def calcLnPartial (fuel : Nat) (x : CalcRat) : CalcRat :=
  let z := calcLnZ x
  let rec go : Nat -> CalcRat
    | 0 => calcLnOddTerm z 0
    | Nat.succ k => calcAdd (go k) (calcLnOddTerm z (Nat.succ k))
  go fuel

def calcLnTailBound (fuel : Nat) (x : CalcRat) : CalcRat :=
  let z := calcLnZ x
  calcMul (calcAdd x calcOne) (calcPow z (2 * fuel + 3))

def calcLnLower (fuel : Nat) (x : CalcRat) : CalcRat :=
  calcLnPartial fuel x

def calcLnUpper (fuel : Nat) (x : CalcRat) : CalcRat :=
  calcAdd (calcLnPartial fuel x) (calcLnTailBound fuel x)

def calcToRaw (x : CalcRat) : RawRat :=
  { num := x.num, denMinusOne := calcDen x - 1 }

def rawToCalc (x : RawRat) : CalcRat :=
  { num := x.num, den := rawDen x }

def rawNormalize (x : RawRat) : RawRat :=
  BEDC.Derived.BernoulliUp.rawNormalize x

def rawOfIntOverNat (num : Int) (den : Nat) : RawRat :=
  match den with
  | 0 => BEDC.Derived.BernoulliUp.rawZero
  | Nat.succ d => { num := num, denMinusOne := d }

def rawOfNat (n : Nat) : RawRat :=
  rawOfIntOverNat (Int.ofNat n) 1

def rawZero : RawRat :=
  rawOfNat 0

def rawOne : RawRat :=
  rawOfNat 1

def rawTwo : RawRat :=
  rawOfNat 2

def rawAdd (x y : RawRat) : RawRat :=
  BEDC.Derived.BernoulliUp.rawAdd x y

def rawNeg (x : RawRat) : RawRat :=
  BEDC.Derived.BernoulliUp.rawNeg x

def rawSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)

def rawMul (x y : RawRat) : RawRat :=
  rawNormalize
    { num := x.num * y.num
      denMinusOne := rawDen x * rawDen y - 1 }

def rawInv (x : RawRat) : RawRat :=
  match x.num with
  | Int.ofNat 0 => rawZero
  | Int.ofNat (Nat.succ n) =>
      rawNormalize { num := Int.ofNat (rawDen x), denMinusOne := n }
  | Int.negSucc n =>
      rawNormalize { num := -Int.ofNat (rawDen x), denMinusOne := n }

def rawDiv (x y : RawRat) : RawRat :=
  rawMul x (rawInv y)

def rawDivByNat (x : RawRat) (n : Nat) : RawRat :=
  match n with
  | 0 => rawZero
  | Nat.succ d => rawNormalize { num := x.num, denMinusOne := rawDen x * Nat.succ d - 1 }

def rawOneOverNat (n : Nat) : RawRat :=
  rawOfIntOverNat 1 n

def rawHarmonic : Nat -> RawRat
  | 0 => rawZero
  | Nat.succ n => rawAdd (rawHarmonic n) (rawOneOverNat (Nat.succ n))

def rawPow (x : RawRat) : Nat -> RawRat
  | 0 => rawOne
  | Nat.succ n => rawMul x (rawPow x n)

def expSeriesTerm (x : RawRat) (k : Nat) : RawRat :=
  rawDivByNat (rawPow x k) (factorial k)

def rawExpPartial (fuel : Nat) (x : RawRat) : RawRat :=
  match fuel with
  | 0 => expSeriesTerm x 0
  | Nat.succ n => rawAdd (rawExpPartial n x) (expSeriesTerm x (Nat.succ n))

def rawExpTailBound (fuel : Nat) (x : RawRat) : RawRat :=
  rawMul (expSeriesTerm x (Nat.succ fuel))
    (rawOfIntOverNat (Int.ofNat (fuel + 2)) 2)

def rawExpLowerBound (fuel : Nat) (x : RawRat) : RawRat :=
  rawExpPartial fuel x

def rawExpUpperBound (fuel : Nat) (x : RawRat) : RawRat :=
  rawAdd (rawExpPartial fuel x) (rawExpTailBound fuel x)

def rawLnZ (x : RawRat) : RawRat :=
  rawDiv (rawSub x rawOne) (rawAdd x rawOne)

def rawLnOddTerm (z : RawRat) (k : Nat) : RawRat :=
  rawMul rawTwo (rawDivByNat (rawPow z (2 * k + 1)) (2 * k + 1))

def rawLnPartial (fuel : Nat) (x : RawRat) : RawRat :=
  let z := rawLnZ x
  let rec go : Nat -> RawRat
    | 0 => rawLnOddTerm z 0
    | Nat.succ k => rawAdd (go k) (rawLnOddTerm z (Nat.succ k))
  go fuel

def rawLnTailBound (fuel : Nat) (x : RawRat) : RawRat :=
  let z := rawLnZ x
  rawMul (rawAdd x rawOne) (rawPow z (2 * fuel + 3))

def rawLnLower (fuel : Nat) (x : RawRat) : RawRat :=
  rawLnPartial fuel x

def rawLnUpper (fuel : Nat) (x : RawRat) : RawRat :=
  rawAdd (rawLnPartial fuel x) (rawLnTailBound fuel x)

def intUpToLeanInt (x : BEDC.Derived.PrimeUp.IntegerUp) : Int :=
  match x.sign with
  | BEDC.FKernel.Mark.BMark.b0 => Int.ofNat (bwordLength x.magnitude)
  | BEDC.FKernel.Mark.BMark.b1 => -Int.ofNat (bwordLength x.magnitude)

def ratToRaw (x : RatNum) : RawRat :=
  rawOfIntOverNat (intUpToLeanInt x.num) (bwordLength x.den)

def rawToRatNum (x : RawRat) : RatNum :=
  BEDC.Derived.BernoulliUp.rawRatToRat x

/--
Finite Taylor lower endpoint for `exp(x)`, returned as a BEDC rational.
The fuel parameter fixes a concrete finite truncation.
-/
def ratExpLowerBound (fuel : Nat) (x : RatNum) : RatNum :=
  rawToRatNum (rawExpLowerBound fuel (ratToRaw x))

/--
Finite Taylor upper endpoint for `exp(x)`, returned as a BEDC rational.
The tail envelope is rational and fuel-bounded.
-/
def ratExpUpperBound (fuel : Nat) (x : RatNum) : RatNum :=
  rawToRatNum (rawExpUpperBound fuel (ratToRaw x))

/--
Finite atanh-series lower endpoint for `ln(x)`, returned as a BEDC rational.
Lagarias applications feed positive harmonic inputs.
-/
def ratLnLower (fuel : Nat) (x : RatNum) : RatNum :=
  rawToRatNum (rawLnLower fuel (ratToRaw x))

/--
Finite atanh-series upper endpoint for `ln(x)`, returned as a BEDC rational.
The endpoint is a computable rational value, not a real-analysis theorem.
-/
def ratLnUpper (fuel : Nat) (x : RatNum) : RatNum :=
  rawToRatNum (rawLnUpper fuel (ratToRaw x))

def dividesBool (d n : Nat) : Bool :=
  match d with
  | 0 => false
  | Nat.succ _ => decide (n % d = 0)

def divisorListNatAux (n : Nat) : Nat -> List BEDC.FKernel.Hist.BHist
  | 0 => []
  | Nat.succ k =>
      let d := Nat.succ k
      let rest := divisorListNatAux n k
      if dividesBool d n then BEDC.Derived.IntUp.natToUnary d :: rest else rest

def divisorListNat (n : Nat) : List BEDC.FKernel.Hist.BHist :=
  divisorListNatAux n n

def sigmaNat (n : Nat) : Nat :=
  bwordLength
    (BEDC.Derived.DivisorFunctionUp.divisorSigmaEnumerationValue 1
      (divisorListNat n))

def sigmaRat (n : Nat) : RatNum :=
  rawToRatNum (rawOfNat (sigmaNat n))

def sigmaRaw (n : Nat) : RawRat :=
  rawOfNat (sigmaNat n)

def rawLeBool (x y : RawRat) : Bool :=
  intLeBool (x.num * Int.ofNat (rawDen y)) (y.num * Int.ofNat (rawDen x))

def ratLeBool (x y : RatNum) : Bool :=
  rawLeBool (ratToRaw x) (ratToRaw y)

def ratLe (x y : RatNum) : Prop :=
  ratLeBool x y = true

def lagariasExpFuel (n : Nat) : Nat :=
  n + 16

def lagariasLogFuel (n : Nat) : Nat :=
  n + 8

def LagariasBoundRaw (n : Nat) : RawRat :=
  let h := calcHarmonic n
  let expUpper := calcExpUpperBound (lagariasExpFuel n) h
  let lnUpper := calcLnUpper (lagariasLogFuel n) h
  calcToRaw (calcAdd h (calcMul expUpper lnUpper))

/--
The public rational surface for the Lagarias right-hand side:
`H_n + exp(H_n) * ln(H_n)` with the transcendental calls replaced by
finite rational upper endpoints.
-/
def LagariasBound (n : Nat) : RatNum :=
  let h := BEDC.Derived.HarmonicUp.harmonic n
  ratAdd h
    (ratMul (ratExpUpperBound (lagariasExpFuel n) h)
      (ratLnUpper (lagariasLogFuel n) h))

/--
`LagariasCriterion` is the BEDC-side constructive, finite rational surface of
the Lagarias route to RH: divisor sums and harmonic numbers are finite, while
the transcendental factors are replaced by explicit rational interval
computations.  The classical equivalence between this inequality and RH is a
Lagarias 2002 analytic-number-theory boundary fact and is not proved here.
-/
def LagariasCriterion : Prop :=
  ∀ n, 1 ≤ n -> ratLe (sigmaRat n) (LagariasBound n)

/--
Fast finite audit predicate for concrete values.  It uses the raw rational
calculation path underlying the same finite Lagarias expression, avoiding
full public `RatNum` evaluation through large unary denominators.
-/
def lagariasHoldsAt (n : Nat) : Prop :=
  rawLeBool (sigmaRaw n) (LagariasBoundRaw n) = true

theorem lagarias_holds_at_one : lagariasHoldsAt 1 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_two : lagariasHoldsAt 2 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_three : lagariasHoldsAt 3 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_four : lagariasHoldsAt 4 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_five : lagariasHoldsAt 5 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_six : lagariasHoldsAt 6 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_seven : lagariasHoldsAt 7 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_eight : lagariasHoldsAt 8 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_nine : lagariasHoldsAt 9 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_ten : lagariasHoldsAt 10 := by
  unfold lagariasHoldsAt
  decide

theorem lagarias_holds_at_small_window :
    lagariasHoldsAt 1 ∧ lagariasHoldsAt 2 ∧ lagariasHoldsAt 3 ∧
      lagariasHoldsAt 4 ∧ lagariasHoldsAt 5 ∧ lagariasHoldsAt 6 ∧
        lagariasHoldsAt 7 ∧ lagariasHoldsAt 8 ∧ lagariasHoldsAt 9 ∧
          lagariasHoldsAt 10 := by
  exact ⟨lagarias_holds_at_one, lagarias_holds_at_two, lagarias_holds_at_three,
    lagarias_holds_at_four, lagarias_holds_at_five, lagarias_holds_at_six,
    lagarias_holds_at_seven, lagarias_holds_at_eight, lagarias_holds_at_nine,
    lagarias_holds_at_ten⟩

end BEDC.Derived.RHRoute.LagariasCriterion
