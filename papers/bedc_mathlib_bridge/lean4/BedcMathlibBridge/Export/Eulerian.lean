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

end BedcMathlibBridge.Export.Eulerian
