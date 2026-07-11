import BedcMathlibBridge.Constructive.Eulerian

/-!
Export witness for the Eulerian row-sum structural correspondence.

The witness records the BEDC Eulerian row-sum readback, its factorial recurrence,
and the pointwise equality with mathlib `Nat.factorial`.
-/

namespace BedcMathlibBridge.Export.Eulerian

open BedcMathlibBridge.Constructive.Eulerian

structure EulerianRowSumExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.EulerianNumberUp.eulerianRowSum n
  zero_apply : readback 0 = 1
  recurrence_apply : ∀ n : Nat, readback (Nat.succ n) = Nat.succ n * readback n
  nat_factorial_apply : ∀ n : Nat, readback n = Nat.factorial n

def eulerianRowSumExport : EulerianRowSumExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ_mul
  nat_factorial_apply := toNat_eq_nat_factorial

theorem eulerianRowSum_eq_nat_factorial (n : Nat) :
    BEDC.Derived.EulerianNumberUp.eulerianRowSum n = Nat.factorial n :=
  BedcMathlibBridge.Constructive.Eulerian.toNat_eq_nat_factorial n

structure EulerianTriangleExportWitness where
  table : Nat -> Nat -> Nat
  table_apply : ∀ n k : Nat, table n k = triangleReadback n k
  bedc_table_apply : ∀ n k : Nat,
    table n k = BEDC.Derived.EulerianNumberUp.eulerianNumber n k
  zero_zero : table 0 0 = 1
  zero_succ : ∀ k : Nat, table 0 (Nat.succ k) = 0
  left_boundary : ∀ n : Nat, table n 0 = 1
  recurrence_apply : ∀ n k : Nat,
    table (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ k)) (table n (Nat.succ k)))
        (Nat.mul (Nat.sub n k) (table n k))
  above_row_zero : ∀ n extra : Nat,
    table n (Nat.succ (n + extra)) = 0
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def eulerianTriangleExport : EulerianTriangleExportWitness where
  table := triangleReadback
  table_apply := by
    intro n k
    rfl
  bedc_table_apply := triangleReadback_apply
  zero_zero := triangle_zero_zero
  zero_succ := triangle_zero_succ
  left_boundary := triangle_left_boundary
  recurrence_apply := triangle_recurrence_nat_mul_add_sub
  above_row_zero := triangle_above_row_zero
  mathlib_anchor := mathlibNatTriangleAnchor

theorem eulerianNumber_recurrence_nat_mul_add_sub
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective :=
      mathlibNatTriangleAnchor) :
    BEDC.Derived.EulerianNumberUp.eulerianNumber
        (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul
          (Nat.succ (Nat.succ k))
          (BEDC.Derived.EulerianNumberUp.eulerianNumber n (Nat.succ k)))
        (Nat.mul
          (Nat.sub n k)
          (BEDC.Derived.EulerianNumberUp.eulerianNumber n k)) := by
  change
    triangleReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ k)) (triangleReadback n (Nat.succ k)))
        (Nat.mul (Nat.sub n k) (triangleReadback n k))
  exact triangle_recurrence_nat_mul_add_sub n k

end BedcMathlibBridge.Export.Eulerian
