import BEDC.Derived.GenocchiUp

namespace BEDC.Derived.GenocchiNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.BernoulliUp
open BEDC.Derived.RationalUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat
abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

def rawMulInt : Int -> RawRat -> RawRat :=
  BEDC.Derived.GenocchiUp.rawMulInt

def powTwo : Nat -> Nat :=
  BEDC.Derived.EulerPolyUp.powTwo

def rawGenocchiNumberScale (n : Nat) : Int :=
  2 * (1 - Int.ofNat (powTwo n))

def rawGenocchiNumber (n : Nat) : RawRat :=
  rawMulInt (rawGenocchiNumberScale n) (rawBernoulli n)

def genocchiNumber (n : Nat) : RatNum :=
  rawRatToRat (rawGenocchiNumber n)

def genocchiNumberUp (n : BHist) : RatNum :=
  genocchiNumber (bwordLength n)

def rawGenocchiNumberIntegralAt (n : Nat) : Prop :=
  (rawGenocchiNumber n).den = 1

def rawGenocchiNumberIntValue (n : Nat) : Int :=
  (rawGenocchiNumber n).num

def genocchiNumberIntegerWitness
    (n : Nat) (_integral : rawGenocchiNumberIntegralAt n) : Int :=
  rawGenocchiNumberIntValue n

def genocchiInteger (n : Nat)
    (integral : rawGenocchiNumberIntegralAt n) : IntegerUp :=
  BEDC.Derived.BernoulliUp.intOfLeanInt
    (genocchiNumberIntegerWitness n integral)

def genocchiIntegerPair (n : Nat)
    (integral : rawGenocchiNumberIntegralAt n) : BHist × BHist :=
  intToPair (genocchiInteger n integral)

def genocchiNumberZero : RatNum :=
  BEDC.Derived.GenocchiUp.genocchiZero

def genocchiNumberOne : RatNum :=
  BEDC.Derived.GenocchiUp.genocchiOne

def genocchiNumberTwo : RatNum :=
  BEDC.Derived.GenocchiUp.genocchiTwo

def genocchiNumberFour : RatNum :=
  BEDC.Derived.GenocchiUp.genocchiFour

def genocchiNumberSix : RatNum :=
  BEDC.Derived.GenocchiUp.genocchiSix

def genocchiNumberEight : RatNum :=
  BEDC.Derived.GenocchiUp.genocchiEight

theorem rawGenocchiNumber_Bernoulli_relation (n : Nat) :
    rawGenocchiNumber n =
      rawMulInt (2 * (1 - Int.ofNat (powTwo n))) (rawBernoulli n) := by
  rfl

theorem genocchiNumber_Bernoulli_relation (n : Nat) :
    genocchiNumber n = rawRatToRat
      (rawMulInt (2 * (1 - Int.ofNat (powTwo n))) (rawBernoulli n)) := by
  rfl

theorem genocchiNumberUp_definition (n : BHist) :
    genocchiNumberUp n = genocchiNumber (bwordLength n) := by
  rfl

theorem rawGenocchiNumber_matches_GenocchiUp (n : Nat) :
    rawGenocchiNumber n = BEDC.Derived.GenocchiUp.rawGenocchi n := by
  rfl

theorem genocchiNumber_matches_GenocchiUp (n : Nat) :
    genocchiNumber n = BEDC.Derived.GenocchiUp.genocchi n := by
  rfl

theorem rawGenocchiNumber_zero_value :
    rawGenocchiNumber 0 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_one_value :
    rawGenocchiNumber 1 = { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_two_value :
    rawGenocchiNumber 2 = { num := -1, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_three_value :
    rawGenocchiNumber 3 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_four_value :
    rawGenocchiNumber 4 = { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_five_value :
    rawGenocchiNumber 5 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_six_value :
    rawGenocchiNumber 6 = { num := -3, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_seven_value :
    rawGenocchiNumber 7 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_eight_value :
    rawGenocchiNumber 8 = { num := 17, denMinusOne := 0 } := by
  rfl

theorem rawGenocchiNumber_zero_integral :
    rawGenocchiNumberIntegralAt 0 := by
  rfl

theorem rawGenocchiNumber_one_integral :
    rawGenocchiNumberIntegralAt 1 := by
  rfl

theorem rawGenocchiNumber_two_integral :
    rawGenocchiNumberIntegralAt 2 := by
  rfl

theorem rawGenocchiNumber_three_integral :
    rawGenocchiNumberIntegralAt 3 := by
  rfl

theorem rawGenocchiNumber_four_integral :
    rawGenocchiNumberIntegralAt 4 := by
  rfl

theorem rawGenocchiNumber_five_integral :
    rawGenocchiNumberIntegralAt 5 := by
  rfl

theorem rawGenocchiNumber_six_integral :
    rawGenocchiNumberIntegralAt 6 := by
  rfl

theorem rawGenocchiNumber_seven_integral :
    rawGenocchiNumberIntegralAt 7 := by
  rfl

theorem rawGenocchiNumber_eight_integral :
    rawGenocchiNumberIntegralAt 8 := by
  rfl

theorem genocchiIntegerPair_carrier (n : Nat)
    (integral : rawGenocchiNumberIntegralAt n) :
    BEDC.Derived.IntUp.IntPairCarrier
      (genocchiIntegerPair n integral).1
      (genocchiIntegerPair n integral).2 := by
  unfold genocchiIntegerPair
  exact BEDC.Derived.RationalUp.intToPair_carrier (genocchiInteger n integral)

theorem genocchiInteger_one_value :
    IntEq
      (genocchiInteger 1 rawGenocchiNumber_one_integral)
      (BEDC.Derived.BernoulliUp.intOfLeanInt 1) := by
  exact BEDC.Derived.RationalUp.IntEq_refl _

theorem genocchiInteger_two_value :
    IntEq
      (genocchiInteger 2 rawGenocchiNumber_two_integral)
      (BEDC.Derived.BernoulliUp.intOfLeanInt (-1)) := by
  exact BEDC.Derived.RationalUp.IntEq_refl _

theorem genocchiInteger_four_value :
    IntEq
      (genocchiInteger 4 rawGenocchiNumber_four_integral)
      (BEDC.Derived.BernoulliUp.intOfLeanInt 1) := by
  exact BEDC.Derived.RationalUp.IntEq_refl _

theorem genocchiInteger_six_value :
    IntEq
      (genocchiInteger 6 rawGenocchiNumber_six_integral)
      (BEDC.Derived.BernoulliUp.intOfLeanInt (-3)) := by
  exact BEDC.Derived.RationalUp.IntEq_refl _

theorem genocchiNumber_zero :
    RatEq (genocchiNumber 0) genocchiNumberZero := by
  exact BEDC.Derived.GenocchiUp.genocchi_zero

theorem genocchiNumber_one :
    RatEq (genocchiNumber 1) genocchiNumberOne := by
  exact BEDC.Derived.GenocchiUp.genocchi_one

theorem genocchiNumber_two :
    RatEq (genocchiNumber 2) genocchiNumberTwo := by
  exact BEDC.Derived.GenocchiUp.genocchi_two

theorem genocchiNumber_four :
    RatEq (genocchiNumber 4) genocchiNumberFour := by
  exact BEDC.Derived.GenocchiUp.genocchi_four

theorem genocchiNumber_six :
    RatEq (genocchiNumber 6) genocchiNumberSix := by
  exact BEDC.Derived.GenocchiUp.genocchi_six

theorem genocchiNumber_eight :
    RatEq (genocchiNumber 8) genocchiNumberEight := by
  exact BEDC.Derived.GenocchiUp.genocchi_eight

theorem rawGenocchiNumber_small_values :
    rawGenocchiNumber 0 = { num := 0, denMinusOne := 0 } ∧
      rawGenocchiNumber 1 = { num := 1, denMinusOne := 0 } ∧
      rawGenocchiNumber 2 = { num := -1, denMinusOne := 0 } ∧
      rawGenocchiNumber 3 = { num := 0, denMinusOne := 0 } ∧
      rawGenocchiNumber 4 = { num := 1, denMinusOne := 0 } ∧
      rawGenocchiNumber 5 = { num := 0, denMinusOne := 0 } ∧
      rawGenocchiNumber 6 = { num := -3, denMinusOne := 0 } ∧
      rawGenocchiNumber 7 = { num := 0, denMinusOne := 0 } ∧
      rawGenocchiNumber 8 = { num := 17, denMinusOne := 0 } := by
  exact ⟨rawGenocchiNumber_zero_value, rawGenocchiNumber_one_value,
    rawGenocchiNumber_two_value, rawGenocchiNumber_three_value,
    rawGenocchiNumber_four_value, rawGenocchiNumber_five_value,
    rawGenocchiNumber_six_value, rawGenocchiNumber_seven_value,
    rawGenocchiNumber_eight_value⟩

theorem rawGenocchiNumber_integral_small_values :
    rawGenocchiNumberIntegralAt 0 ∧
      rawGenocchiNumberIntegralAt 1 ∧
      rawGenocchiNumberIntegralAt 2 ∧
      rawGenocchiNumberIntegralAt 3 ∧
      rawGenocchiNumberIntegralAt 4 ∧
      rawGenocchiNumberIntegralAt 5 ∧
      rawGenocchiNumberIntegralAt 6 ∧
      rawGenocchiNumberIntegralAt 7 ∧
      rawGenocchiNumberIntegralAt 8 := by
  exact ⟨rawGenocchiNumber_zero_integral, rawGenocchiNumber_one_integral,
    rawGenocchiNumber_two_integral, rawGenocchiNumber_three_integral,
    rawGenocchiNumber_four_integral, rawGenocchiNumber_five_integral,
    rawGenocchiNumber_six_integral, rawGenocchiNumber_seven_integral,
    rawGenocchiNumber_eight_integral⟩

theorem genocchiNumber_small_values :
    RatEq (genocchiNumber 0) genocchiNumberZero ∧
      RatEq (genocchiNumber 1) genocchiNumberOne ∧
      RatEq (genocchiNumber 2) genocchiNumberTwo ∧
      RatEq (genocchiNumber 4) genocchiNumberFour ∧
      RatEq (genocchiNumber 6) genocchiNumberSix ∧
      RatEq (genocchiNumber 8) genocchiNumberEight := by
  exact ⟨genocchiNumber_zero, genocchiNumber_one, genocchiNumber_two,
    genocchiNumber_four, genocchiNumber_six, genocchiNumber_eight⟩

end BEDC.Derived.GenocchiNumberUp
