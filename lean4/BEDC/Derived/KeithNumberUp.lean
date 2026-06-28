import BEDC.Derived.FibonacciUp
import BEDC.Derived.HarshadNumberUp
import BEDC.Derived.HappyNumberUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.KeithNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

def decimalBase : Nat := 10

abbrev keithDigitSum (digits : List Nat) : Nat :=
  BEDC.Derived.HarshadNumberUp.digitSum decimalBase digits

def keithDigits (value : Nat) : List Nat :=
  (BEDC.Derived.HappyNumberUp.natDigitsLsb decimalBase value).reverse

structure KeithState where
  window : List Nat
  sequence : List Nat

-- 窗口按从旧到新的顺序保存最近的数字; 下一项是整个窗口之和。
def keithStateStep (state : KeithState) : KeithState :=
  let next := keithDigitSum state.window
  { window := state.window.tail ++ [next],
    sequence := state.sequence ++ [next] }

def keithStateFuel (digits : List Nat) : Nat -> KeithState
  | 0 => { window := digits, sequence := digits }
  | fuel + 1 => keithStateStep (keithStateFuel digits fuel)

def keithWindowFuel (digits : List Nat) (fuel : Nat) : List Nat :=
  (keithStateFuel digits fuel).window

def keithSequenceFuel (digits : List Nat) (fuel : Nat) : List Nat :=
  (keithStateFuel digits fuel).sequence

def keithNextValue (digits : List Nat) (fuel : Nat) : Nat :=
  keithDigitSum (keithWindowFuel digits fuel)

def KeithHitsWithin (fuel value : Nat) (digits : List Nat) : Prop :=
  BEDC.Derived.HappyNumberUp.containsNat value (keithSequenceFuel digits fuel)

def KeithNumberWithFuel (fuel value : Nat) : Prop :=
  1 < (keithDigits value).length ∧ KeithHitsWithin fuel value (keithDigits value)

instance keithHitsWithinDecidable (fuel value : Nat) (digits : List Nat) :
    Decidable (KeithHitsWithin fuel value digits) :=
  inferInstanceAs
    (Decidable
      (0 < BEDC.Derived.HappyNumberUp.countNat value (keithSequenceFuel digits fuel)))

instance keithNumberWithFuelDecidable (fuel value : Nat) :
    Decidable (KeithNumberWithFuel fuel value) :=
  inferInstanceAs
    (Decidable
      (1 < (keithDigits value).length ∧
        KeithHitsWithin fuel value (keithDigits value)))

def KeithNumber (value : Nat) : Prop :=
  ∃ fuel : Nat, KeithNumberWithFuel fuel value

abbrev Keith := KeithNumber

def keithWithinBool (fuel value : Nat) : Bool :=
  if KeithNumberWithFuel fuel value then true else false

def keithNextValueUp (digits : List Nat) (fuel : Nat) : BHist :=
  natToUnary (keithNextValue digits fuel)

theorem keithDigitSum_nil :
    keithDigitSum [] = 0 := by
  rfl

theorem keithDigitSum_cons (digit : Nat) (rest : List Nat) :
    keithDigitSum (digit :: rest) = digit + keithDigitSum rest := by
  rfl

theorem keithDigitSum_decimal_digit_sum (digits : List Nat) :
    keithDigitSum digits =
      BEDC.Derived.HarshadNumberUp.digitSum decimalBase digits := by
  rfl

theorem keithStateFuel_zero (digits : List Nat) :
    keithSequenceFuel digits 0 = digits := by
  rfl

theorem keithWindowFuel_zero (digits : List Nat) :
    keithWindowFuel digits 0 = digits := by
  rfl

theorem keithSequenceFuel_succ (digits : List Nat) (fuel : Nat) :
    keithSequenceFuel digits (fuel + 1) =
      keithSequenceFuel digits fuel ++ [keithNextValue digits fuel] := by
  rfl

theorem keithWindowFuel_succ (digits : List Nat) (fuel : Nat) :
    keithWindowFuel digits (fuel + 1) =
      (keithWindowFuel digits fuel).tail ++ [keithNextValue digits fuel] := by
  rfl

theorem keithNextValue_eq_window_sum (digits : List Nat) (fuel : Nat) :
    keithNextValue digits fuel = keithDigitSum (keithWindowFuel digits fuel) := by
  rfl

theorem keithWithinBool_true_iff (fuel value : Nat) :
    keithWithinBool fuel value = true ↔ KeithNumberWithFuel fuel value := by
  constructor
  · intro h
    unfold keithWithinBool at h
    by_cases hk : KeithNumberWithFuel fuel value
    · exact hk
    · rw [if_neg hk] at h
      cases h
  · intro hk
    unfold keithWithinBool
    rw [if_pos hk]

theorem keithNextValueUp_unary (digits : List Nat) (fuel : Nat) :
    UnaryHistory (keithNextValueUp digits fuel) := by
  unfold keithNextValueUp
  exact natToUnary_unary (keithNextValue digits fuel)

theorem keithNextValueUp_length (digits : List Nat) (fuel : Nat) :
    bwordLength (keithNextValueUp digits fuel) = keithNextValue digits fuel := by
  unfold keithNextValueUp
  exact natToUnary_length (keithNextValue digits fuel)

theorem keithDigits_fourteen :
    keithDigits 14 = [1, 4] := by
  rfl

theorem keithDigits_nineteen :
    keithDigits 19 = [1, 9] := by
  rfl

theorem keithDigits_twentyEight :
    keithDigits 28 = [2, 8] := by
  rfl

theorem keithSequence_digits_fourteen :
    keithSequenceFuel [1, 4] 3 = [1, 4, 5, 9, 14] := by
  rfl

theorem keithSequence_digits_nineteen :
    keithSequenceFuel [1, 9] 2 = [1, 9, 10, 19] := by
  rfl

theorem keithSequence_digits_twentyEight :
    keithSequenceFuel [2, 8] 3 = [2, 8, 10, 18, 28] := by
  rfl

theorem keithSequence_zero_one_fibonacci_prefix :
    keithSequenceFuel [0, 1] 4 =
      [BEDC.Derived.FibonacciUp.fib 0,
        BEDC.Derived.FibonacciUp.fib 1,
        BEDC.Derived.FibonacciUp.fib 2,
        BEDC.Derived.FibonacciUp.fib 3,
        BEDC.Derived.FibonacciUp.fib 4,
        BEDC.Derived.FibonacciUp.fib 5] := by
  rfl

theorem keith_fourteen_withFuel :
    KeithNumberWithFuel 3 14 := by
  decide

theorem keith_nineteen_withFuel :
    KeithNumberWithFuel 2 19 := by
  decide

theorem keith_twentyEight_withFuel :
    KeithNumberWithFuel 3 28 := by
  decide

theorem keith_fourteen :
    KeithNumber 14 := by
  exact ⟨3, keith_fourteen_withFuel⟩

theorem keith_nineteen :
    KeithNumber 19 := by
  exact ⟨2, keith_nineteen_withFuel⟩

theorem keith_twentyEight :
    KeithNumber 28 := by
  exact ⟨3, keith_twentyEight_withFuel⟩

theorem keith_small_decimal_values :
    KeithNumber 14 ∧ KeithNumber 19 ∧ KeithNumber 28 := by
  exact ⟨keith_fourteen, keith_nineteen, keith_twentyEight⟩

theorem keithWithinBool_fourteen :
    keithWithinBool 3 14 = true := by
  exact (keithWithinBool_true_iff 3 14).mpr keith_fourteen_withFuel

theorem keithWithinBool_nineteen :
    keithWithinBool 2 19 = true := by
  exact (keithWithinBool_true_iff 2 19).mpr keith_nineteen_withFuel

theorem keithWithinBool_twentyEight :
    keithWithinBool 3 28 = true := by
  exact (keithWithinBool_true_iff 3 28).mpr keith_twentyEight_withFuel

end BEDC.Derived.KeithNumberUp
