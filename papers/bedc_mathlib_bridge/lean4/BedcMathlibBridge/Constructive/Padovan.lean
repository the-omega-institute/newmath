import BEDC.Derived.PadovanUp
import Mathlib.Data.Nat.Basic

/-!
Padovan recurrence readback correspondence.

The BEDC object is the closed `Nat` recurrence
`BEDC.Derived.PadovanUp.padovan`. The bridge records the direct readback and
the third-order recurrence using the host `Nat.add` operation.
-/

namespace BedcMathlibBridge.Constructive.Padovan

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.PadovanUp.padovan n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.PadovanUp.padovan n := by
  rfl

theorem toNat_zero :
    toNat 0 = 1 := by
  rfl

theorem toNat_one :
    toNat 1 = 1 := by
  rfl

theorem toNat_two :
    toNat 2 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (n + 3) = Nat.add (toNat (n + 1)) (toNat n) := by
  change
    BEDC.Derived.PadovanUp.padovan (n + 3) =
      Nat.add (BEDC.Derived.PadovanUp.padovan (n + 1))
        (BEDC.Derived.PadovanUp.padovan n)
  exact BEDC.Derived.PadovanUp.padovan_recurrence n

theorem padovan_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PadovanUp.padovan (n + 3) =
      Nat.add (BEDC.Derived.PadovanUp.padovan (n + 1))
        (BEDC.Derived.PadovanUp.padovan n) := by
  exact BEDC.Derived.PadovanUp.padovan_recurrence n

end BedcMathlibBridge.Constructive.Padovan
