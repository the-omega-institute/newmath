import BedcMathlibBridge.Constructive.LahSecondColumn

/-!
Export witness for the Lah second-column closed numerator and denominator
surface.
-/

namespace BedcMathlibBridge.Export.LahSecondColumn

open BedcMathlibBridge.Constructive.LahSecondColumn

structure LahSecondColumnExportWitness where
  readback : Nat -> Nat
  numeratorReadback : Nat -> Nat
  denominatorReadback : Nat
  readback_apply : forall n : Nat, readback n = secondColumnReadback n
  bedc_readback_apply : forall n : Nat,
    readback n =
      BEDC.Derived.LahNumberUp.lahNumber (Nat.succ (Nat.succ n)) 2
  numerator_apply : forall n : Nat,
    numeratorReadback n = secondColumnClosedNumeratorReadback n
  bedc_numerator_apply : forall n : Nat,
    numeratorReadback n =
      BEDC.Derived.LahNumberUp.lahClosedNumerator
        (Nat.succ (Nat.succ n)) 2
  bedc_denominator_apply :
    denominatorReadback = BEDC.Derived.LahNumberUp.lahClosedDenominator 2
  mathlib_numerator_apply : forall n : Nat,
    numeratorReadback n =
      Nat.choose (Nat.succ n) 1 * Nat.factorial (Nat.succ (Nat.succ n))
  mathlib_denominator_apply :
    denominatorReadback = Nat.factorial 2

def lahSecondColumnExport : LahSecondColumnExportWitness where
  readback := secondColumnReadback
  numeratorReadback := secondColumnClosedNumeratorReadback
  denominatorReadback := secondColumnClosedDenominatorReadback
  readback_apply := by
    intro n
    rfl
  bedc_readback_apply := secondColumnReadback_apply
  numerator_apply := by
    intro n
    rfl
  bedc_numerator_apply := secondColumnClosedNumerator_apply
  bedc_denominator_apply := secondColumnClosedDenominator_apply
  mathlib_numerator_apply := secondColumnClosedNumerator_eq_mathlib
  mathlib_denominator_apply := secondColumnClosedDenominator_eq_mathlib

theorem lah_second_column_closed_numerator_eq_nat_choose_factorial (n : Nat) :
    BEDC.Derived.LahNumberUp.lahClosedNumerator
        (Nat.succ (Nat.succ n)) 2 =
      Nat.choose (Nat.succ n) 1 * Nat.factorial (Nat.succ (Nat.succ n)) :=
  secondColumnClosedNumerator_eq_nat_choose_factorial n

end BedcMathlibBridge.Export.LahSecondColumn
