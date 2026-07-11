import BedcMathlibBridge.Constructive.BellTriangle

/-!
Export witness for the Bell recurrence triangle `Nat.choose` correspondence.
-/

namespace BedcMathlibBridge.Export.BellTriangle

open BedcMathlibBridge.Constructive.BellTriangle

structure BellTriangleExportWitness where
  chooseReadback : Nat -> Nat -> Nat
  recurrencePrefixReadback : (Nat -> Nat) -> Nat -> Nat -> Nat
  recurrenceReadback : Nat -> Nat
  choose_apply : forall n k : Nat,
    chooseReadback n k =
      BEDC.Derived.BellNumberUp.natChooseCount n k
  choose_nat_apply : forall n k : Nat, chooseReadback n k = Nat.choose n k
  prefix_apply : forall (B : Nat -> Nat) (n k : Nat),
    recurrencePrefixReadback B n k =
      BEDC.Derived.BellNumberUp.bellRecurrencePrefix B n k
  readback_apply : forall n : Nat,
    recurrenceReadback n =
      BEDC.Derived.BellNumberUp.bellNumberByRecurrence n
  prefix_zero : forall (B : Nat -> Nat) (n : Nat),
    recurrencePrefixReadback B n 0 = Nat.choose n 0 * B 0
  prefix_succ : forall (B : Nat -> Nat) (n k : Nat),
    recurrencePrefixReadback B n (Nat.succ k) =
      recurrencePrefixReadback B n k + Nat.choose n (Nat.succ k) * B (Nat.succ k)
  recurrence_succ : forall n : Nat,
    recurrenceReadback (Nat.succ n) =
      recurrencePrefixReadback recurrenceReadback n n
  mathlib_choose_recurrence : forall n : Nat,
    recurrenceReadback (Nat.succ n) =
        recurrencePrefixReadback recurrenceReadback n n ∧
      (forall k : Nat,
        recurrencePrefixReadback recurrenceReadback n (Nat.succ k) =
          recurrencePrefixReadback recurrenceReadback n k +
            Nat.choose n (Nat.succ k) * recurrenceReadback (Nat.succ k))

def bellTriangleExport : BellTriangleExportWitness where
  chooseReadback := chooseReadback
  recurrencePrefixReadback := recurrencePrefixReadback
  recurrenceReadback := recurrenceReadback
  choose_apply := chooseReadback_apply
  choose_nat_apply := chooseReadback_eq_nat_choose
  prefix_apply := recurrencePrefixReadback_apply
  readback_apply := recurrenceReadback_apply
  prefix_zero := recurrencePrefixReadback_zero_nat_choose
  prefix_succ := recurrencePrefixReadback_succ_nat_choose
  recurrence_succ := recurrenceReadback_succ
  mathlib_choose_recurrence := bellNumberByRecurrence_mathlib_choose_recurrence_readback

theorem bellNumberByRecurrence_mathlib_choose_recurrence (n : Nat) :
    BEDC.Derived.BellNumberUp.bellNumberByRecurrence (Nat.succ n) =
        BEDC.Derived.BellNumberUp.bellRecurrencePrefix
          BEDC.Derived.BellNumberUp.bellNumberByRecurrence n n ∧
      (forall k : Nat,
        BEDC.Derived.BellNumberUp.bellRecurrencePrefix
            BEDC.Derived.BellNumberUp.bellNumberByRecurrence n (Nat.succ k) =
          BEDC.Derived.BellNumberUp.bellRecurrencePrefix
            BEDC.Derived.BellNumberUp.bellNumberByRecurrence n k +
            Nat.choose n (Nat.succ k) *
              BEDC.Derived.BellNumberUp.bellNumberByRecurrence (Nat.succ k)) := by
  simpa [recurrenceReadback, recurrencePrefixReadback]
    using
      BedcMathlibBridge.Constructive.BellTriangle.bellNumberByRecurrence_mathlib_choose_recurrence_readback n

end BedcMathlibBridge.Export.BellTriangle
