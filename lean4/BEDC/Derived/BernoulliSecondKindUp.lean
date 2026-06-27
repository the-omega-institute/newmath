import BEDC.Derived.BernoulliUp
import BEDC.Derived.StirlingFirstUp

namespace BEDC.Derived.BernoulliSecondKindUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.RationalUp
open BEDC.Derived.BernoulliUp
open BEDC.Derived.StirlingFirstUp

abbrev unaryOne : BHist := BHist.e1 BHist.Empty

-- Gregory 系数使用有符号第一类 Stirling 数的有限和定义。
def signedGap : Nat -> Int
  | 0 => 1
  | Nat.succ n => -signedGap n

def signedStirlingFirst (n k : Nat) : Int :=
  signedGap (n - k) * Int.ofNat (stirlingFirst n k)

def rawStirlingFirstGregoryTerm (n k : Nat) : RawRat :=
  rawNormalize
    { num := signedStirlingFirst n k
      denMinusOne := factorialNat n * Nat.succ k - 1 }

def rawStirlingFirstGregorySum (n : Nat) : Nat -> Nat -> RawRat
  | 0, _ => rawZero
  | Nat.succ fuel, k =>
      rawAdd (rawStirlingFirstGregoryTerm n k)
        (rawStirlingFirstGregorySum n fuel (Nat.succ k))

def rawBernoulliSecondKind (n : Nat) : RawRat :=
  rawStirlingFirstGregorySum n (Nat.succ n) 0

def bernoulliSecondKind (n : Nat) : RatNum :=
  rawRatToRat (rawBernoulliSecondKind n)

def bernoulliSecondKindUp (n : BHist) : RatNum :=
  bernoulliSecondKind (bwordLength n)

def bernoulliSecondKindZero : RatNum :=
  ratOfIntOverNat 1 0

def bernoulliSecondKindOne : RatNum :=
  ratOfIntOverNat 1 1

def bernoulliSecondKindTwo : RatNum :=
  ratOfIntOverNat (-1) 11

def bernoulliSecondKindThree : RatNum :=
  ratOfIntOverNat 1 23

def bernoulliSecondKindFour : RatNum :=
  ratOfIntOverNat (-19) 719

theorem signedGap_zero :
    signedGap 0 = 1 := by
  rfl

theorem signedGap_succ (n : Nat) :
    signedGap (Nat.succ n) = -signedGap n := by
  rfl

theorem signedStirlingFirst_definition (n k : Nat) :
    signedStirlingFirst n k =
      signedGap (n - k) * Int.ofNat (stirlingFirst n k) := by
  rfl

theorem rawStirlingFirstGregoryTerm_definition (n k : Nat) :
    rawStirlingFirstGregoryTerm n k =
      rawNormalize
        { num := signedStirlingFirst n k
          denMinusOne := factorialNat n * Nat.succ k - 1 } := by
  rfl

theorem rawStirlingFirstGregorySum_zero_fuel (n k : Nat) :
    rawStirlingFirstGregorySum n 0 k = rawZero := by
  rfl

theorem rawStirlingFirstGregorySum_succ_fuel (n fuel k : Nat) :
    rawStirlingFirstGregorySum n (Nat.succ fuel) k =
      rawAdd (rawStirlingFirstGregoryTerm n k)
        (rawStirlingFirstGregorySum n fuel (Nat.succ k)) := by
  rfl

theorem rawBernoulliSecondKind_stirlingFirst_formula (n : Nat) :
    rawBernoulliSecondKind n =
      rawStirlingFirstGregorySum n (Nat.succ n) 0 := by
  rfl

theorem rawBernoulliSecondKind_zero_value :
    rawBernoulliSecondKind 0 = { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawBernoulliSecondKind_one_value :
    rawBernoulliSecondKind 1 = { num := 1, denMinusOne := 1 } := by
  rfl

theorem rawBernoulliSecondKind_two_value :
    rawBernoulliSecondKind 2 = { num := -1, denMinusOne := 11 } := by
  rfl

theorem rawBernoulliSecondKind_three_value :
    rawBernoulliSecondKind 3 = { num := 1, denMinusOne := 23 } := by
  rfl

theorem rawBernoulliSecondKind_four_value :
    rawBernoulliSecondKind 4 = { num := -19, denMinusOne := 719 } := by
  rfl

theorem rawBernoulliSecondKind_zero_matches_first_kind :
    rawBernoulliSecondKind 0 = rawBernoulli 0 := by
  rfl

theorem rawBernoulliSecondKind_one_negates_first_kind :
    rawBernoulliSecondKind 1 = rawNeg (rawBernoulli 1) := by
  rfl

theorem bernoulliSecondKind_zero :
    RatEq (bernoulliSecondKind 0) bernoulliSecondKindZero := by
  simpa [bernoulliSecondKind, bernoulliSecondKindZero, ratOfIntOverNat,
    rawBernoulliSecondKind_zero_value] using
    RatEq_refl bernoulliSecondKindZero

theorem bernoulliSecondKind_one :
    RatEq (bernoulliSecondKind 1) bernoulliSecondKindOne := by
  simpa [bernoulliSecondKind, bernoulliSecondKindOne, ratOfIntOverNat,
    rawBernoulliSecondKind_one_value] using
    RatEq_refl bernoulliSecondKindOne

theorem bernoulliSecondKind_two :
    RatEq (bernoulliSecondKind 2) bernoulliSecondKindTwo := by
  simpa [bernoulliSecondKind, bernoulliSecondKindTwo, ratOfIntOverNat,
    rawBernoulliSecondKind_two_value] using
    RatEq_refl bernoulliSecondKindTwo

theorem bernoulliSecondKind_three :
    RatEq (bernoulliSecondKind 3) bernoulliSecondKindThree := by
  simpa [bernoulliSecondKind, bernoulliSecondKindThree, ratOfIntOverNat,
    rawBernoulliSecondKind_three_value] using
    RatEq_refl bernoulliSecondKindThree

theorem bernoulliSecondKind_four :
    RatEq (bernoulliSecondKind 4) bernoulliSecondKindFour := by
  simpa [bernoulliSecondKind, bernoulliSecondKindFour, ratOfIntOverNat,
    rawBernoulliSecondKind_four_value] using
    RatEq_refl bernoulliSecondKindFour

theorem bernoulliSecondKind_small_values :
    RatEq (bernoulliSecondKind 0) bernoulliSecondKindZero ∧
      RatEq (bernoulliSecondKind 1) bernoulliSecondKindOne ∧
      RatEq (bernoulliSecondKind 2) bernoulliSecondKindTwo ∧
      RatEq (bernoulliSecondKind 3) bernoulliSecondKindThree ∧
      RatEq (bernoulliSecondKind 4) bernoulliSecondKindFour := by
  exact ⟨bernoulliSecondKind_zero, bernoulliSecondKind_one,
    bernoulliSecondKind_two, bernoulliSecondKind_three,
    bernoulliSecondKind_four⟩

theorem bernoulliSecondKindUp_unary_nat (n : Nat) :
    bernoulliSecondKindUp (natToUnary n) = bernoulliSecondKind n := by
  unfold bernoulliSecondKindUp
  rw [natToUnary_length]

theorem bernoulliSecondKindUp_unary_result (n : BHist) :
    RatEq (bernoulliSecondKindUp n) (bernoulliSecondKind (bwordLength n)) := by
  exact RatEq_refl (bernoulliSecondKind (bwordLength n))

end BEDC.Derived.BernoulliSecondKindUp
