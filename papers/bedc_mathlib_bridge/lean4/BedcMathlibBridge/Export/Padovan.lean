import BedcMathlibBridge.Constructive.Padovan

/-!
Export witness for the Padovan recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.Padovan

open BedcMathlibBridge.Constructive.Padovan

structure PadovanExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.PadovanUp.padovan n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 1
  two_apply : readback 2 = 1
  recurrence_apply : forall n : Nat,
    readback (n + 3) = Nat.add (readback (n + 1)) (readback n)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def padovanExport : PadovanExportWitness where
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

theorem padovan_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PadovanUp.padovan (n + 3) =
      Nat.add (BEDC.Derived.PadovanUp.padovan (n + 1))
        (BEDC.Derived.PadovanUp.padovan n) :=
  BedcMathlibBridge.Constructive.Padovan.padovan_recurrence_nat_add n

end BedcMathlibBridge.Export.Padovan
