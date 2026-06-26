import BEDC.Derived.RationalUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.BernoulliUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.RationalUp

abbrev unaryOne : BHist := BHist.e1 BHist.Empty

structure RawRat where
  num : Int
  denMinusOne : Nat
  deriving DecidableEq, Repr

def RawRat.den (x : RawRat) : Nat :=
  Nat.succ x.denMinusOne

def intAbsNat : Int -> Nat
  | Int.ofNat n => n
  | Int.negSucc n => Nat.succ n

def rawNormalize (x : RawRat) : RawRat :=
  let divisor := Nat.gcd (intAbsNat x.num) x.den
  { num := x.num / Int.ofNat divisor
    denMinusOne := x.den / divisor - 1 }

def rawZero : RawRat :=
  { num := 0, denMinusOne := 0 }

def rawOne : RawRat :=
  { num := 1, denMinusOne := 0 }

def rawNeg (x : RawRat) : RawRat :=
  rawNormalize { num := -x.num, denMinusOne := x.denMinusOne }

def rawAdd (x y : RawRat) : RawRat :=
  rawNormalize
    { num := x.num * Int.ofNat y.den + y.num * Int.ofNat x.den
      denMinusOne := x.den * y.den - 1 }

def rawMulNat (n : Nat) (x : RawRat) : RawRat :=
  rawNormalize
    { num := Int.ofNat n * x.num
      denMinusOne := x.denMinusOne }

def rawScaleDen (x : RawRat) (factorMinusOne : Nat) : RawRat :=
  rawNormalize
    { num := x.num
      denMinusOne := x.den * Nat.succ factorMinusOne - 1 }

def binomNat (n k : Nat) : Nat :=
  bwordLength
    (BEDC.Derived.FactorialUp.natChooseFn (natToUnary n) (natToUnary k))

def rawBernoulliSum (row : Nat) : List RawRat -> Nat -> RawRat
  | [], _ => rawZero
  | b :: bs, k =>
      rawAdd (rawMulNat (binomNat row k) b)
        (rawBernoulliSum row bs (Nat.succ k))

def rawBernoulliNext (n : Nat) (previous : List RawRat) : RawRat :=
  rawNeg (rawScaleDen (rawBernoulliSum (Nat.succ n) previous 0) n)

def rawBernoulliPair : Nat -> List RawRat × RawRat
  | 0 => ([rawOne], rawOne)
  | Nat.succ n =>
      let previous := rawBernoulliPair n
      let next := rawBernoulliNext (Nat.succ n) previous.1
      (previous.1 ++ [next], next)

def rawBernoulliTable (n : Nat) : List RawRat :=
  (rawBernoulliPair n).1

def rawBernoulli (n : Nat) : RawRat :=
  (rawBernoulliPair n).2

def intOfLeanInt : Int -> BEDC.Derived.PrimeUp.IntegerUp
  | Int.ofNat n =>
      { sign := BMark.b0
        magnitude := natToUnary n
        carrier := ⟨Or.inl rfl, natToUnary_unary n⟩ }
  | Int.negSucc n =>
      { sign := BMark.b1
        magnitude := natToUnary (Nat.succ n)
        carrier := ⟨Or.inr rfl, natToUnary_unary (Nat.succ n)⟩ }

theorem natToUnary_one_left_cont (n : Nat) :
    Cont unaryOne (natToUnary n) (natToUnary (Nat.succ n)) := by
  induction n with
  | zero =>
      rfl
  | succ _ ih =>
      change BHist.e1 (natToUnary _) =
        BHist.e1 (append unaryOne _)
      exact congrArg BHist.e1 ih

def denPosOfMinusOne : (d : Nat) ->
    NatUnaryStrictPrefix unaryOne (natToUnary (Nat.succ d)) ∨
      hsame (natToUnary (Nat.succ d)) unaryOne
  | 0 => Or.inr rfl
  | Nat.succ d =>
      Or.inl
        ⟨natToUnary (Nat.succ d), natToUnary_unary (Nat.succ d),
          (fun empty => by cases empty),
          natToUnary_one_left_cont (Nat.succ d)⟩

def rawRatToRat (x : RawRat) : RatNum :=
  { num := intOfLeanInt x.num
    den := natToUnary x.den
    den_pos := denPosOfMinusOne x.denMinusOne }

def ratOfIntOverNat (num : Int) (denMinusOne : Nat) : RatNum :=
  rawRatToRat { num := num, denMinusOne := denMinusOne }

def bernoulli (n : Nat) : RatNum :=
  rawRatToRat (rawBernoulli n)

def bernoulliUp (n : BHist) : RatNum :=
  bernoulli (bwordLength n)

def bernoulliRowSum (n : Nat) : RawRat :=
  rawBernoulliSum (Nat.succ n) (rawBernoulliTable (n - 1)) 0

theorem rawBernoulliTable_zero :
    rawBernoulliTable 0 = [rawOne] := by
  rfl

theorem rawBernoulliTable_succ (n : Nat) :
    rawBernoulliTable (Nat.succ n) =
      rawBernoulliTable n ++
        [rawBernoulliNext (Nat.succ n) (rawBernoulliTable n)] := by
  rfl

theorem rawBernoulli_succ (n : Nat) :
    rawBernoulli (Nat.succ n) =
      rawBernoulliNext (Nat.succ n) (rawBernoulliTable n) := by
  rfl

theorem rawBernoulli_zero_value :
    rawBernoulli 0 = { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawBernoulli_one_value :
    rawBernoulli 1 = { num := -1, denMinusOne := 1 } := by
  rfl

theorem rawBernoulli_two_value :
    rawBernoulli 2 = { num := 1, denMinusOne := 5 } := by
  rfl

theorem rawBernoulli_four_raw_value :
    rawBernoulli 4 = { num := -1, denMinusOne := 29 } := by
  rfl

def bernoulliZero : RatNum :=
  ratOfIntOverNat 1 0

def bernoulliOne : RatNum :=
  ratOfIntOverNat (-1) 1

def bernoulliTwo : RatNum :=
  ratOfIntOverNat 1 5

def bernoulliFour : RatNum :=
  ratOfIntOverNat (-1) 29

theorem bernoulli_zero :
    RatEq (bernoulli 0) bernoulliZero := by
  simpa [bernoulli, bernoulliZero, ratOfIntOverNat, rawBernoulli_zero_value]
    using RatEq_refl bernoulliZero

theorem bernoulli_one :
    RatEq (bernoulli 1) bernoulliOne := by
  simpa [bernoulli, bernoulliOne, ratOfIntOverNat, rawBernoulli_one_value]
    using RatEq_refl bernoulliOne

theorem bernoulli_two :
    RatEq (bernoulli 2) bernoulliTwo := by
  simpa [bernoulli, bernoulliTwo, ratOfIntOverNat, rawBernoulli_two_value]
    using RatEq_refl bernoulliTwo

theorem bernoulli_four :
    RatEq (bernoulli 4) bernoulliFour := by
  simpa [bernoulli, bernoulliFour, ratOfIntOverNat, rawBernoulli_four_raw_value]
    using RatEq_refl bernoulliFour

theorem bernoulli_small_values :
    RatEq (bernoulli 0) bernoulliZero ∧
      RatEq (bernoulli 1) bernoulliOne ∧
      RatEq (bernoulli 2) bernoulliTwo ∧
      RatEq (bernoulli 4) bernoulliFour := by
  exact ⟨bernoulli_zero, bernoulli_one, bernoulli_two, bernoulli_four⟩

end BEDC.Derived.BernoulliUp
