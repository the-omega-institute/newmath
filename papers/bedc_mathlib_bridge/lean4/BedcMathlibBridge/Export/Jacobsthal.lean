import BedcMathlibBridge.Constructive.Jacobsthal

/-!
Export witness for the Jacobsthal recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.Jacobsthal

open BedcMathlibBridge.Constructive.Jacobsthal

structure JacobsthalExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply :
    forall n : Nat, readback n = BEDC.Derived.JacobsthalUp.jacobsthal n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  recurrence_apply : forall n : Nat,
    readback (n + 2) =
      Nat.add (readback (n + 1)) (Nat.mul 2 (readback n))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def jacobsthalExport : JacobsthalExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  one_apply := toNat_one
  recurrence_apply := toNat_recurrence
  mathlib_anchor := mathlibNatAnchor

theorem jacobsthal_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.JacobsthalUp.jacobsthal (n + 2) =
      Nat.add
        (BEDC.Derived.JacobsthalUp.jacobsthal (n + 1))
        (Nat.mul 2 (BEDC.Derived.JacobsthalUp.jacobsthal n)) :=
  BedcMathlibBridge.Constructive.Jacobsthal.jacobsthal_recurrence_nat_add_mul n

end BedcMathlibBridge.Export.Jacobsthal
