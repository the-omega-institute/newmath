import BedcMathlibBridge.Constructive.LahClosedForm

/-!
Export witness for the Lah diagonal closed-form correspondence.
-/

namespace BedcMathlibBridge.Export.LahClosedForm

open BedcMathlibBridge.Constructive.LahClosedForm

structure LahClosedFormExportWitness where
  readback : Nat -> Nat
  numeratorReadback : Nat -> Nat
  denominatorReadback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = diagonalReadback n
  bedc_apply : forall n : Nat,
    readback n =
      BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ n)
  diagonal_apply : forall n : Nat, readback n = 1
  numerator_apply : forall n : Nat,
    numeratorReadback n =
      BEDC.Derived.LahNumberUp.lahClosedNumerator
        (Nat.succ n) (Nat.succ n)
  denominator_apply : forall n : Nat,
    denominatorReadback n =
      BEDC.Derived.LahNumberUp.lahClosedDenominator (Nat.succ n)
  mathlib_numerator_apply : forall n : Nat,
    numeratorReadback n = Nat.choose n n * Nat.factorial (Nat.succ n)
  mathlib_denominator_apply : forall n : Nat,
    denominatorReadback n = Nat.factorial (Nat.succ n)
  exact_closed_division : forall n : Nat,
    readback n * denominatorReadback n = numeratorReadback n
  mathlib_closed_division : forall n : Nat,
    readback n * Nat.factorial (Nat.succ n) =
      Nat.choose n n * Nat.factorial (Nat.succ n)

def lahClosedFormExport : LahClosedFormExportWitness where
  readback := diagonalReadback
  numeratorReadback := diagonalClosedNumeratorReadback
  denominatorReadback := diagonalClosedDenominatorReadback
  readback_apply := by
    intro n
    rfl
  bedc_apply := diagonalReadback_apply
  diagonal_apply := diagonal_eq_one
  numerator_apply := by
    intro n
    rfl
  denominator_apply := by
    intro n
    rfl
  mathlib_numerator_apply := diagonal_closed_numerator_eq_mathlib
  mathlib_denominator_apply := diagonal_closed_denominator_eq_mathlib
  exact_closed_division := diagonal_exact_closed_division
  mathlib_closed_division := diagonal_mathlib_closed_division

theorem lah_diagonal_mathlib_closed_division (n : Nat) :
    BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ n) *
        Nat.factorial (Nat.succ n) =
      Nat.choose n n * Nat.factorial (Nat.succ n) :=
  BedcMathlibBridge.Constructive.LahClosedForm.diagonal_mathlib_closed_division n

end BedcMathlibBridge.Export.LahClosedForm
