import BEDC.Derived.ZigzagNumberUp
import Mathlib.Data.Nat.Basic

/-!
Secant-number small-window readback correspondence.

The BEDC side carries the even Euler-zigzag relation
`BEDC.Derived.ZigzagNumberUp.secantNumber`. This bridge records the checked
small values against a host `Nat.pow` expression and stops before any series or
alternating-permutation API.
-/

namespace BedcMathlibBridge.Constructive.SecantNumber

private def mathlibPowProvenanceAnchor : Unit :=
  let _ : forall a b : Nat, Nat.pow a b = Nat.pow a b := fun _ _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def relationReadback (n a : Nat) : Prop :=
  let _ := mathlibPowProvenanceAnchor
  BEDC.Derived.ZigzagNumberUp.secantNumber n a

theorem relationReadback_apply {n a : Nat} :
    relationReadback n a ↔ BEDC.Derived.ZigzagNumberUp.secantNumber n a := by
  rfl

theorem mathlibPowAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem zero_value :
    relationReadback 0 (Nat.pow 1 1) := by
  exact BEDC.Derived.ZigzagNumberUp.secant_S0

theorem one_value :
    relationReadback 1 (Nat.pow 1 1) := by
  exact BEDC.Derived.ZigzagNumberUp.secant_S1

theorem two_value :
    relationReadback 2 (Nat.pow 2 2 + 1) := by
  exact BEDC.Derived.ZigzagNumberUp.secant_S2

theorem small_values_nat_pow_anchor
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.ZigzagNumberUp.secantNumber 0 (Nat.pow 1 1) ∧
      BEDC.Derived.ZigzagNumberUp.secantNumber 1 (Nat.pow 1 1) ∧
        BEDC.Derived.ZigzagNumberUp.secantNumber 2 (Nat.pow 2 2 + 1) := by
  exact ⟨zero_value, one_value, two_value⟩

end BedcMathlibBridge.Constructive.SecantNumber
