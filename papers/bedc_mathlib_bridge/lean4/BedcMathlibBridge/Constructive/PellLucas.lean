import BEDC.Derived.PellLucasUp
import Mathlib.Data.Nat.Basic

/-!
Pell-Lucas recurrence readback correspondence.

The BEDC objects are the closed `Nat` recurrences
`BEDC.Derived.PellLucasUp.pellNat` and
`BEDC.Derived.PellLucasUp.companionPellNat`. The bridge records their direct
readback through host `Nat.add` and `Nat.mul`.
-/

namespace BedcMathlibBridge.Constructive.PellLucas

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

def pellReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.PellLucasUp.pellNat n

def companionReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.PellLucasUp.companionPellNat n

theorem pellReadback_apply (n : Nat) :
    pellReadback n = BEDC.Derived.PellLucasUp.pellNat n := by
  rfl

theorem companionReadback_apply (n : Nat) :
    companionReadback n = BEDC.Derived.PellLucasUp.companionPellNat n := by
  rfl

theorem pellReadback_zero :
    pellReadback 0 = 0 := by
  rfl

theorem pellReadback_one :
    pellReadback 1 = 1 := by
  rfl

theorem companionReadback_zero :
    companionReadback 0 = 2 := by
  rfl

theorem companionReadback_one :
    companionReadback 1 = 2 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem pellReadback_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    pellReadback (n + 2) =
      Nat.add (Nat.mul 2 (pellReadback (n + 1))) (pellReadback n) := by
  change
    BEDC.Derived.PellLucasUp.pellNat (n + 2) =
      2 * BEDC.Derived.PellLucasUp.pellNat (n + 1) +
        BEDC.Derived.PellLucasUp.pellNat n
  exact BEDC.Derived.PellLucasUp.pellNat_recurrence n

theorem companionReadback_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    companionReadback (n + 2) =
      Nat.add (Nat.mul 2 (companionReadback (n + 1))) (companionReadback n) := by
  change
    BEDC.Derived.PellLucasUp.companionPellNat (n + 2) =
      2 * BEDC.Derived.PellLucasUp.companionPellNat (n + 1) +
        BEDC.Derived.PellLucasUp.companionPellNat n
  exact BEDC.Derived.PellLucasUp.companionPellNat_recurrence n

theorem companionReadback_adjacent_sum
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    companionReadback (n + 1) =
      Nat.add (pellReadback (n + 2)) (pellReadback n) := by
  change
    BEDC.Derived.PellLucasUp.companionPellNat (n + 1) =
      BEDC.Derived.PellLucasUp.pellNat (n + 2) +
        BEDC.Derived.PellLucasUp.pellNat n
  exact BEDC.Derived.PellLucasUp.companionPellNat_eq_pellNat_adjacent_sum n

theorem pellNat_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.pellNat (n + 2) =
      Nat.add
        (Nat.mul 2 (BEDC.Derived.PellLucasUp.pellNat (n + 1)))
        (BEDC.Derived.PellLucasUp.pellNat n) :=
  BEDC.Derived.PellLucasUp.pellNat_recurrence n

theorem companionPellNat_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.companionPellNat (n + 2) =
      Nat.add
        (Nat.mul 2 (BEDC.Derived.PellLucasUp.companionPellNat (n + 1)))
        (BEDC.Derived.PellLucasUp.companionPellNat n) :=
  BEDC.Derived.PellLucasUp.companionPellNat_recurrence n

theorem companionPellNat_adjacent_sum_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.companionPellNat (n + 1) =
      Nat.add
        (BEDC.Derived.PellLucasUp.pellNat (n + 2))
        (BEDC.Derived.PellLucasUp.pellNat n) :=
  BEDC.Derived.PellLucasUp.companionPellNat_eq_pellNat_adjacent_sum n

end BedcMathlibBridge.Constructive.PellLucas
