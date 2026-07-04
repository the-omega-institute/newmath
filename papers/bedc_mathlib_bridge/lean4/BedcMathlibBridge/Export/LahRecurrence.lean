import BedcMathlibBridge.Constructive.LahRecurrence

/-!
Export witness for the Lah table recurrence readback.
-/

namespace BedcMathlibBridge.Export.LahRecurrence

open BedcMathlibBridge.Constructive.LahRecurrence

structure LahRecurrenceExportWitness where
  tableReadback : Nat -> Nat -> Nat
  rowPrefixReadback : Nat -> Nat -> Nat
  rowSumReadback : Nat -> Nat
  table_apply : forall n k : Nat,
    tableReadback n k = BEDC.Derived.LahNumberUp.lahNumber n k
  row_prefix_apply : forall n k : Nat,
    rowPrefixReadback n k = BEDC.Derived.LahNumberUp.lahRowPrefix n k
  row_sum_apply : forall n : Nat,
    rowSumReadback n = BEDC.Derived.LahNumberUp.lahRowSum n
  table_zero_zero : tableReadback 0 0 = 1
  table_zero_succ : forall k : Nat, tableReadback 0 (Nat.succ k) = 0
  table_succ_zero : forall n : Nat, tableReadback (Nat.succ n) 0 = 0
  table_recurrence : forall n k : Nat,
    tableReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.add n (Nat.succ k))
          (tableReadback n (Nat.succ k)))
        (tableReadback n k)
  table_self : forall n : Nat, tableReadback n n = 1
  table_above : forall n extra : Nat,
    tableReadback n (Nat.succ (n + extra)) = 0
  row_prefix_succ : forall n k : Nat,
    rowPrefixReadback n (Nat.succ k) =
      Nat.add (rowPrefixReadback n k)
        (tableReadback n (Nat.succ k))
  row_sum_definition : forall n : Nat,
    rowSumReadback n = rowPrefixReadback n n
  row_prefix_above : forall n extra : Nat,
    rowPrefixReadback n (n + extra) = rowSumReadback n
  row_prefix_recurrence : forall n k : Nat,
    rowPrefixReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (rowPrefixReadback (Nat.succ n) k)
        (Nat.add
          (Nat.mul (Nat.add n (Nat.succ k))
            (tableReadback n (Nat.succ k)))
          (tableReadback n k))
  row_sum_small_values :
    rowSumReadback 0 = 1 ∧ rowSumReadback 1 = 1 ∧
      rowSumReadback 2 = 3 ∧ rowSumReadback 3 = 13
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def lahRecurrenceExport : LahRecurrenceExportWitness where
  tableReadback := tableReadback
  rowPrefixReadback := rowPrefixReadback
  rowSumReadback := rowSumReadback
  table_apply := tableReadback_apply
  row_prefix_apply := rowPrefixReadback_apply
  row_sum_apply := rowSumReadback_apply
  table_zero_zero := table_zero_zero
  table_zero_succ := table_zero_succ
  table_succ_zero := table_succ_zero
  table_recurrence := table_recurrence_nat_add_mul
  table_self := table_self
  table_above := table_above
  row_prefix_succ := rowPrefix_succ_nat_add
  row_sum_definition := rowSum_definition
  row_prefix_above := rowPrefix_above_self
  row_prefix_recurrence := rowPrefix_succ_row_recurrence_nat_add_mul
  row_sum_small_values := rowSum_small_values
  mathlib_anchor := mathlibNatAnchor

theorem lahNumber_table_recurrence_nat_add_mul
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.add n (Nat.succ k))
          (BEDC.Derived.LahNumberUp.lahNumber n (Nat.succ k)))
        (BEDC.Derived.LahNumberUp.lahNumber n k) :=
  BedcMathlibBridge.Constructive.LahRecurrence.lahNumber_table_recurrence_nat_add_mul n k

end BedcMathlibBridge.Export.LahRecurrence
