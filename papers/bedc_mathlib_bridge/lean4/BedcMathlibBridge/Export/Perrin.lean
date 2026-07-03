import BedcMathlibBridge.Constructive.Perrin

/-!
Export witness for the Perrin recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.Perrin

open BedcMathlibBridge.Constructive.Perrin

structure PerrinExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.PerrinUp.perrin n
  zero_apply : readback 0 = 3
  one_apply : readback 1 = 0
  two_apply : readback 2 = 2
  recurrence_apply : forall n : Nat,
    readback (n + 3) = Nat.add (readback (n + 1)) (readback n)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def perrinExport : PerrinExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  one_apply := toNat_one
  two_apply := toNat_two
  recurrence_apply := toNat_recurrence
  mathlib_anchor := mathlibNatAnchor

theorem perrin_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PerrinUp.perrin (n + 3) =
      Nat.add (BEDC.Derived.PerrinUp.perrin (n + 1))
        (BEDC.Derived.PerrinUp.perrin n) :=
  BedcMathlibBridge.Constructive.Perrin.perrin_recurrence_nat_add n

end BedcMathlibBridge.Export.Perrin
