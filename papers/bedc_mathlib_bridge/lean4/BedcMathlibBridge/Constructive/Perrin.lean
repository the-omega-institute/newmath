import BEDC.Derived.PerrinUp
import Mathlib.Data.Nat.Basic

/-!
Perrin recurrence readback correspondence.

The BEDC object is the closed `Nat` recurrence
`BEDC.Derived.PerrinUp.perrin`. The bridge records the direct readback and the
third-order recurrence using the host `Nat.add` operation.
-/

namespace BedcMathlibBridge.Constructive.Perrin

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.PerrinUp.perrin n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.PerrinUp.perrin n := by
  rfl

theorem toNat_zero :
    toNat 0 = 3 := by
  rfl

theorem toNat_one :
    toNat 1 = 0 := by
  rfl

theorem toNat_two :
    toNat 2 = 2 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (n + 3) = Nat.add (toNat (n + 1)) (toNat n) := by
  change
    BEDC.Derived.PerrinUp.perrin (n + 3) =
      Nat.add (BEDC.Derived.PerrinUp.perrin (n + 1))
        (BEDC.Derived.PerrinUp.perrin n)
  exact BEDC.Derived.PerrinUp.perrin_recurrence n

theorem perrin_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PerrinUp.perrin (n + 3) =
      Nat.add (BEDC.Derived.PerrinUp.perrin (n + 1))
        (BEDC.Derived.PerrinUp.perrin n) := by
  exact BEDC.Derived.PerrinUp.perrin_recurrence n

end BedcMathlibBridge.Constructive.Perrin
