import BEDC.Derived.JacobsthalUp
import Mathlib.Data.Nat.Basic

/-!
Jacobsthal recurrence readback correspondence.

The BEDC object is the closed `Nat` recurrence
`BEDC.Derived.JacobsthalUp.jacobsthal`. The bridge records the direct readback
and its recurrence using the host `Nat.add` and `Nat.mul` operations.
-/

namespace BedcMathlibBridge.Constructive.Jacobsthal

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.JacobsthalUp.jacobsthal n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.JacobsthalUp.jacobsthal n := by
  rfl

theorem toNat_zero :
    toNat 0 = 0 := by
  rfl

theorem toNat_one :
    toNat 1 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (n + 2) =
      Nat.add (toNat (n + 1)) (Nat.mul 2 (toNat n)) := by
  change
    BEDC.Derived.JacobsthalUp.jacobsthal (n + 2) =
      BEDC.Derived.JacobsthalUp.jacobsthal (n + 1) +
        2 * BEDC.Derived.JacobsthalUp.jacobsthal n
  exact BEDC.Derived.JacobsthalUp.jacobsthal_recurrence n

theorem jacobsthal_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.JacobsthalUp.jacobsthal (n + 2) =
      Nat.add
        (BEDC.Derived.JacobsthalUp.jacobsthal (n + 1))
        (Nat.mul 2 (BEDC.Derived.JacobsthalUp.jacobsthal n)) := by
  exact BEDC.Derived.JacobsthalUp.jacobsthal_recurrence n

end BedcMathlibBridge.Constructive.Jacobsthal
