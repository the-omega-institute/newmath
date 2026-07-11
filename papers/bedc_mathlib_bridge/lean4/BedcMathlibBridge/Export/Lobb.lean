import BedcMathlibBridge.Constructive.Lobb

/-!
Export witness for the Lobb number structural correspondence.

The witness records the BEDC readback, the Catalan left edge, and the pointwise
binomial-difference equality against mathlib's `Nat.choose`.
-/

namespace BedcMathlibBridge.Export.Lobb

open BedcMathlibBridge.Constructive.Lobb

structure LobbExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : forall m n : Nat, readback m n = toNat m n
  bedc_apply : forall m n : Nat,
    readback m n = BEDC.Derived.LobbUp.lobbNat m n
  zero_left_apply : forall n : Nat,
    readback 0 n = BEDC.Derived.LobbUp.catalanNat n
  nat_choose_apply :
    forall m n : Nat,
      readback m n =
        Nat.choose (n + n) (n + m) - Nat.choose (n + n) (Nat.succ (n + m))

def lobbExport : LobbExportWitness where
  readback := toNat
  readback_apply := by
    intro m n
    rfl
  bedc_apply := toNat_apply
  zero_left_apply := toNat_zero_left
  nat_choose_apply := toNat_eq_nat_choose_diff

theorem lobbNat_eq_nat_choose_diff (m n : Nat) :
    BEDC.Derived.LobbUp.lobbNat m n =
      Nat.choose (n + n) (n + m) - Nat.choose (n + n) (Nat.succ (n + m)) :=
  BedcMathlibBridge.Constructive.Lobb.toNat_eq_nat_choose_diff m n

end BedcMathlibBridge.Export.Lobb
