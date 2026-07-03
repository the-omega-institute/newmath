import BEDC.Derived.SylvesterSequenceUp
import Mathlib.Data.Nat.Basic

/-!
Sylvester sequence recurrence readback.

The bridge exposes the BEDC `Nat` recurrence and prefix-product identity through
host `Nat` arithmetic, without exporting pairwise coprimality or rational-series
surfaces.
-/

namespace BedcMathlibBridge.Constructive.SylvesterSequence

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : forall a b : Nat, Nat.mul a b = a * b := fun _ _ => rfl
  let _ : forall a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  let _ : forall a b : Nat, Nat.add a b = a + b := fun _ _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SylvesterSequenceUp.sylvester n

def prefixProductReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SylvesterSequenceUp.prefixProduct n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.SylvesterSequenceUp.sylvester n := by
  rfl

theorem prefixProductReadback_apply (n : Nat) :
    prefixProductReadback n =
      BEDC.Derived.SylvesterSequenceUp.prefixProduct n := by
  rfl

theorem toNat_zero :
    toNat 0 = 2 := by
  rfl

theorem prefixProductReadback_zero :
    prefixProductReadback 0 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem sylvester_succ_recurrence_nat_mul_sub_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (n + 1) =
      Nat.add (Nat.sub (Nat.mul (toNat n) (toNat n)) (toNat n)) 1 := by
  change
    BEDC.Derived.SylvesterSequenceUp.sylvester (n + 1) =
      BEDC.Derived.SylvesterSequenceUp.sylvester n *
          BEDC.Derived.SylvesterSequenceUp.sylvester n -
        BEDC.Derived.SylvesterSequenceUp.sylvester n + 1
  exact BEDC.Derived.SylvesterSequenceUp.sylvester_succ_recurrence n

theorem prefixProduct_succ_nat_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    prefixProductReadback (n + 1) =
      Nat.mul (prefixProductReadback n) (toNat n) := by
  change
    BEDC.Derived.SylvesterSequenceUp.prefixProduct (n + 1) =
      BEDC.Derived.SylvesterSequenceUp.prefixProduct n *
        BEDC.Derived.SylvesterSequenceUp.sylvester n
  exact BEDC.Derived.SylvesterSequenceUp.prefixProduct_succ n

theorem toNat_eq_prefixProduct_add_one
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat n = Nat.add (prefixProductReadback n) 1 := by
  change
    BEDC.Derived.SylvesterSequenceUp.sylvester n =
      BEDC.Derived.SylvesterSequenceUp.prefixProduct n + 1
  exact BEDC.Derived.SylvesterSequenceUp.sylvester_eq_prefixProduct_succ n

end BedcMathlibBridge.Constructive.SylvesterSequence
