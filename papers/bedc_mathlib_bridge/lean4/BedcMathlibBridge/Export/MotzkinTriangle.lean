import BedcMathlibBridge.Constructive.MotzkinTriangle

/-!
Export witness for the Motzkin triangle recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.MotzkinTriangle

open BedcMathlibBridge.Constructive.MotzkinTriangle

structure MotzkinTriangleExportWitness where
  triangle : Nat -> Nat -> Nat
  number : Nat -> Nat
  rowSum : Nat -> Nat
  triangle_apply : forall n k : Nat, triangle n k = readback n k
  number_apply : forall n : Nat, number n = numberReadback n
  row_sum_apply : forall n : Nat, rowSum n = rowSumReadback n
  bedc_triangle_apply :
    forall n k : Nat,
      triangle n k = BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n k
  bedc_number_apply :
    forall n : Nat, number n = BEDC.Derived.MotzkinTriangleUp.motzkinNumber n
  bedc_row_sum_apply :
    forall n : Nat,
      rowSum n = BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum n
  zero_zero : triangle 0 0 = 1
  zero_succ : forall k : Nat, triangle 0 (Nat.succ k) = 0
  zero_step_apply : forall n : Nat,
    triangle (Nat.succ n) 0 = Nat.add (triangle n 0) (triangle n 1)
  recurrence_apply : forall n k : Nat,
    triangle (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.add (triangle n k) (triangle n (Nat.succ k)))
        (triangle n (Nat.succ (Nat.succ k)))
  zero_column_apply : forall n : Nat, triangle n 0 = number n
  row_sum_prefix_apply : forall n : Nat,
    rowSum n = BEDC.Derived.MotzkinTriangleUp.motzkinTrianglePrefix n n
  zero_column_small :
    number 0 = 1 ∧ number 1 = 1 ∧ number 2 = 2 ∧
      number 3 = 4 ∧ number 4 = 9 ∧ number 5 = 21
  row_sum_small :
    rowSum 0 = 1 ∧ rowSum 1 = 2 ∧ rowSum 2 = 5 ∧ rowSum 3 = 13
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def motzkinTriangleExport : MotzkinTriangleExportWitness where
  triangle := readback
  number := numberReadback
  rowSum := rowSumReadback
  triangle_apply := by
    intro n k
    rfl
  number_apply := by
    intro n
    rfl
  row_sum_apply := by
    intro n
    rfl
  bedc_triangle_apply := readback_apply
  bedc_number_apply := numberReadback_apply
  bedc_row_sum_apply := rowSumReadback_apply
  zero_zero := readback_zero_zero
  zero_succ := readback_zero_succ
  zero_step_apply := readback_zero_step_nat_add
  recurrence_apply := readback_recurrence_nat_add
  zero_column_apply := readback_zero_eq_number
  row_sum_prefix_apply := rowSumReadback_prefix
  zero_column_small := numberReadback_small_zero_column
  row_sum_small := rowSumReadback_small_values
  mathlib_anchor := mathlibNatAnchor

theorem motzkinTriangle_recurrence_nat_add
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangle (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.add
          (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n k)
          (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n (Nat.succ k)))
        (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n
          (Nat.succ (Nat.succ k))) :=
  BedcMathlibBridge.Constructive.MotzkinTriangle.readback_recurrence_nat_add n k

end BedcMathlibBridge.Export.MotzkinTriangle
