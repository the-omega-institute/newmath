import BEDC.Derived.BernoulliUp
import BEDC.Derived.EulerPolyUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.GenocchiUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.BernoulliUp
open BEDC.Derived.RationalUp

def rawMulInt (z : Int) (x : RawRat) : RawRat :=
  rawNormalize { num := z * x.num, denMinusOne := x.denMinusOne }

def rawGenocchiScale (n : Nat) : Int :=
  2 * (1 - Int.ofNat (BEDC.Derived.EulerPolyUp.powTwo n))

def rawGenocchi (n : Nat) : RawRat :=
  rawMulInt (rawGenocchiScale n) (rawBernoulli n)

def genocchi (n : Nat) : RatNum :=
  rawRatToRat (rawGenocchi n)

def genocchiUp (n : BHist) : RatNum :=
  genocchi (bwordLength n)

def rawGenocchiIntegral (n : Nat) : Prop :=
  (rawGenocchi n).den = 1

def rawGenocchiIntValue (n : Nat) : Int :=
  (rawGenocchi n).num

def genocchiIntegerWitness (n : Nat) (_h : rawGenocchiIntegral n) : Int :=
  rawGenocchiIntValue n

def genocchiZero : RatNum :=
  ratOfIntOverNat 0 0

def genocchiOne : RatNum :=
  ratOfIntOverNat 1 0

def genocchiTwo : RatNum :=
  ratOfIntOverNat (-1) 0

def genocchiFour : RatNum :=
  ratOfIntOverNat 1 0

def genocchiSix : RatNum :=
  ratOfIntOverNat (-3) 0

def genocchiEight : RatNum :=
  ratOfIntOverNat 17 0

theorem rawGenocchi_definition (n : Nat) :
    rawGenocchi n =
      rawMulInt (2 * (1 - Int.ofNat (BEDC.Derived.EulerPolyUp.powTwo n)))
        (rawBernoulli n) := by
  rfl

theorem genocchi_definition (n : Nat) :
    genocchi n = rawRatToRat (rawGenocchi n) := by
  rfl

theorem genocchiUp_definition (n : BHist) :
    genocchiUp n = genocchi (bwordLength n) := by
  rfl

theorem rawGenocchi_zero_value :
    rawGenocchi 0 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_one_value :
    rawGenocchi 1 = { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_two_value :
    rawGenocchi 2 = { num := -1, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_three_value :
    rawGenocchi 3 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_four_value :
    rawGenocchi 4 = { num := 1, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_five_value :
    rawGenocchi 5 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_six_value :
    rawGenocchi 6 = { num := -3, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_seven_value :
    rawGenocchi 7 = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_eight_value :
    rawGenocchi 8 = { num := 17, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_zero_integral :
    rawGenocchiIntegral 0 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_zero_value]
  rfl

theorem rawGenocchi_one_integral :
    rawGenocchiIntegral 1 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_one_value]
  rfl

theorem rawGenocchi_two_integral :
    rawGenocchiIntegral 2 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_two_value]
  rfl

theorem rawGenocchi_three_integral :
    rawGenocchiIntegral 3 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_three_value]
  rfl

theorem rawGenocchi_four_integral :
    rawGenocchiIntegral 4 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_four_value]
  rfl

theorem rawGenocchi_five_integral :
    rawGenocchiIntegral 5 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_five_value]
  rfl

theorem rawGenocchi_six_integral :
    rawGenocchiIntegral 6 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_six_value]
  rfl

theorem rawGenocchi_seven_integral :
    rawGenocchiIntegral 7 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_seven_value]
  rfl

theorem rawGenocchi_eight_integral :
    rawGenocchiIntegral 8 := by
  unfold rawGenocchiIntegral
  rw [rawGenocchi_eight_value]
  rfl

theorem genocchi_zero :
    RatEq (genocchi 0) genocchiZero := by
  simpa [genocchi, genocchiZero, ratOfIntOverNat, rawGenocchi_zero_value]
    using RatEq_refl genocchiZero

theorem genocchi_one :
    RatEq (genocchi 1) genocchiOne := by
  simpa [genocchi, genocchiOne, ratOfIntOverNat, rawGenocchi_one_value]
    using RatEq_refl genocchiOne

theorem genocchi_two :
    RatEq (genocchi 2) genocchiTwo := by
  simpa [genocchi, genocchiTwo, ratOfIntOverNat, rawGenocchi_two_value]
    using RatEq_refl genocchiTwo

theorem genocchi_four :
    RatEq (genocchi 4) genocchiFour := by
  simpa [genocchi, genocchiFour, ratOfIntOverNat, rawGenocchi_four_value]
    using RatEq_refl genocchiFour

theorem genocchi_six :
    RatEq (genocchi 6) genocchiSix := by
  simpa [genocchi, genocchiSix, ratOfIntOverNat, rawGenocchi_six_value]
    using RatEq_refl genocchiSix

theorem genocchi_eight :
    RatEq (genocchi 8) genocchiEight := by
  simpa [genocchi, genocchiEight, ratOfIntOverNat, rawGenocchi_eight_value]
    using RatEq_refl genocchiEight

theorem rawGenocchi_small_values :
    rawGenocchi 2 = { num := -1, denMinusOne := 0 } ∧
      rawGenocchi 4 = { num := 1, denMinusOne := 0 } ∧
      rawGenocchi 6 = { num := -3, denMinusOne := 0 } ∧
      rawGenocchi 8 = { num := 17, denMinusOne := 0 } := by
  exact ⟨rawGenocchi_two_value, rawGenocchi_four_value,
    rawGenocchi_six_value, rawGenocchi_eight_value⟩

theorem genocchi_small_values :
    RatEq (genocchi 2) genocchiTwo ∧
      RatEq (genocchi 4) genocchiFour ∧
      RatEq (genocchi 6) genocchiSix ∧
      RatEq (genocchi 8) genocchiEight := by
  exact ⟨genocchi_two, genocchi_four, genocchi_six, genocchi_eight⟩

theorem rawGenocchi_integral_small_values :
    rawGenocchiIntegral 1 ∧
      rawGenocchiIntegral 2 ∧
      rawGenocchiIntegral 3 ∧
      rawGenocchiIntegral 4 ∧
      rawGenocchiIntegral 5 ∧
      rawGenocchiIntegral 6 ∧
      rawGenocchiIntegral 7 ∧
      rawGenocchiIntegral 8 := by
  exact ⟨rawGenocchi_one_integral, rawGenocchi_two_integral,
    rawGenocchi_three_integral, rawGenocchi_four_integral,
    rawGenocchi_five_integral, rawGenocchi_six_integral,
    rawGenocchi_seven_integral, rawGenocchi_eight_integral⟩

theorem rawGenocchi_odd_three_zero :
    rawGenocchi (2 * 1 + 1) = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_odd_five_zero :
    rawGenocchi (2 * 2 + 1) = { num := 0, denMinusOne := 0 } := by
  rfl

theorem rawGenocchi_odd_seven_zero :
    rawGenocchi (2 * 3 + 1) = { num := 0, denMinusOne := 0 } := by
  rfl

theorem eulerOddNumber_one_zero :
    BEDC.Derived.EulerPolyUp.rawEulerNumberByIndex (2 * 0 + 1) =
      BEDC.Derived.EulerPolyUp.rawZero := by
  rfl

theorem eulerOddNumber_three_zero :
    BEDC.Derived.EulerPolyUp.rawEulerNumberByIndex (2 * 1 + 1) =
      BEDC.Derived.EulerPolyUp.rawZero := by
  rfl

theorem eulerOddNumber_five_zero :
    BEDC.Derived.EulerPolyUp.rawEulerNumberByIndex (2 * 2 + 1) =
      BEDC.Derived.EulerPolyUp.rawZero := by
  rfl

theorem genocchiEulerOddZeroAgreement_small :
    rawGenocchi (2 * 1 + 1) =
        BEDC.Derived.EulerPolyUp.rawEulerNumberByIndex (2 * 1 + 1) ∧
      rawGenocchi (2 * 2 + 1) =
        BEDC.Derived.EulerPolyUp.rawEulerNumberByIndex (2 * 2 + 1) := by
  exact ⟨rawGenocchi_odd_three_zero, rawGenocchi_odd_five_zero⟩

end BEDC.Derived.GenocchiUp
