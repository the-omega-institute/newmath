import BedcMathlibBridge.Constructive.EulerianSecondOrder

/-!
Export witness for the second-order Eulerian recurrence readback.
-/

namespace BedcMathlibBridge.Export.EulerianSecondOrder

open BedcMathlibBridge.Constructive.EulerianSecondOrder

structure EulerianSecondOrderExportWitness where
  table : Nat -> Nat -> Nat
  rowSum : Nat -> Nat
  table_apply : forall n k : Nat, table n k = tableReadback n k
  row_sum_apply : forall n : Nat, rowSum n = rowSumReadback n
  bedc_table_apply :
    forall n k : Nat,
      table n k =
        BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n k
  bedc_row_sum_apply :
    forall n : Nat,
      rowSum n =
        BEDC.Derived.EulerianSecondOrderUp.eulerianSecondRowSum n
  zero_zero : table 0 0 = 1
  zero_succ : forall k : Nat, table 0 (Nat.succ k) = 0
  left_boundary : forall n : Nat, table n 0 = 1
  recurrence_apply : forall n k : Nat,
    table (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ k)) (table n (Nat.succ k)))
        (Nat.mul (Nat.sub (Nat.succ (n + n)) (Nat.succ k)) (table n k))
  above_row_zero : forall n extra : Nat,
    table n (Nat.succ (n + extra)) = 0
  row_sum_recurrence_apply : forall n : Nat,
    rowSum (Nat.succ n) = Nat.mul (Nat.succ (n + n)) (rowSum n)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def eulerianSecondOrderExport : EulerianSecondOrderExportWitness where
  table := tableReadback
  rowSum := rowSumReadback
  table_apply := by
    intro n k
    rfl
  row_sum_apply := by
    intro n
    rfl
  bedc_table_apply := tableReadback_apply
  bedc_row_sum_apply := rowSumReadback_apply
  zero_zero := table_zero_zero
  zero_succ := table_zero_succ
  left_boundary := table_left_boundary
  recurrence_apply := table_recurrence_nat_mul_add_sub
  above_row_zero := table_above_row_zero
  row_sum_recurrence_apply := rowSum_succ_nat_mul
  mathlib_anchor := mathlibNatAnchor

theorem eulerianSecondNumber_recurrence_nat_mul_add_sub
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber
        (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul
          (Nat.succ (Nat.succ k))
          (BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n
            (Nat.succ k)))
        (Nat.mul
          (Nat.sub (Nat.succ (n + n)) (Nat.succ k))
          (BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n k)) := by
  change
    tableReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ k)) (tableReadback n (Nat.succ k)))
        (Nat.mul (Nat.sub (Nat.succ (n + n)) (Nat.succ k))
          (tableReadback n k))
  exact table_recurrence_nat_mul_add_sub n k

end BedcMathlibBridge.Export.EulerianSecondOrder
