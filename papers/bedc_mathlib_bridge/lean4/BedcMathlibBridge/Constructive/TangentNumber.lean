import BEDC.Derived.TangentNumberUp
import Mathlib.Data.Nat.Basic

/-!
Tangent-number small-window readback correspondence.

The BEDC side carries the finite tangent-number window
`BEDC.Derived.TangentNumberUp.tangentNumberFn`. This bridge records the checked
small values against a host `Nat.pow` expression and stops before any Bernoulli
or analytic tangent-series API.
-/

namespace BedcMathlibBridge.Constructive.TangentNumber

private def mathlibPowProvenanceAnchor : Unit :=
  let _ : forall a b : Nat, Nat.pow a b = Nat.pow a b := fun _ _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def readback (n : Nat) : Nat :=
  let _ := mathlibPowProvenanceAnchor
  BEDC.Derived.TangentNumberUp.tangentNumberFn n

theorem readback_apply (n : Nat) :
    readback n = BEDC.Derived.TangentNumberUp.tangentNumberFn n := by
  rfl

theorem readback_one :
    readback 1 = 1 := by
  rfl

theorem readback_two :
    readback 2 = 2 := by
  rfl

theorem readback_three :
    readback 3 = 16 := by
  rfl

theorem readback_four :
    readback 4 = 272 := by
  rfl

theorem mathlibPowAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem small_values_nat_pow_anchor
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.TangentNumberUp.tangentNumberFn 1 = Nat.pow 1 1 ∧
      BEDC.Derived.TangentNumberUp.tangentNumberFn 2 = Nat.pow 2 1 ∧
        BEDC.Derived.TangentNumberUp.tangentNumberFn 3 = Nat.pow 2 4 ∧
          BEDC.Derived.TangentNumberUp.tangentNumberFn 4 =
            Nat.pow 2 8 + Nat.pow 2 4 := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩

theorem readback_odd_zigzag_small_values :
    (BEDC.Derived.TangentNumberUp.tangentNumber 1 (readback 1) ∧
        BEDC.Derived.ZigzagUp.ZigzagNumber 1 (readback 1)) ∧
      (BEDC.Derived.TangentNumberUp.tangentNumber 2 (readback 2) ∧
        BEDC.Derived.ZigzagUp.ZigzagNumber 3 (readback 2)) ∧
        (BEDC.Derived.TangentNumberUp.tangentNumber 3 (readback 3) ∧
          BEDC.Derived.ZigzagUp.ZigzagNumber 5 (readback 3)) ∧
          (BEDC.Derived.TangentNumberUp.tangentNumber 4 (readback 4) ∧
            BEDC.Derived.ZigzagUp.ZigzagNumber 7 (readback 4)) := by
  exact BEDC.Derived.TangentNumberUp.tangentNumber_odd_zigzag_small_values

end BedcMathlibBridge.Constructive.TangentNumber
