import BEDC.Derived.HyperfactorialUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.Hyperfactorial

private def natPowProvenanceAnchor : Unit :=
  let _ : forall k : Nat, k ^ k = Nat.pow k k := fun _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def toNat (n : Nat) : Nat :=
  let _ := natPowProvenanceAnchor
  BEDC.Derived.HyperfactorialUp.hyperfactorial n

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) =
      toNat n * BEDC.Derived.HyperfactorialUp.hyperfactorialTerm (Nat.succ n) := by
  rfl

theorem mathlibPowAnchor : Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem hyperfactorialTerm_eq_nat_pow
    (k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.HyperfactorialUp.hyperfactorialTerm k = Nat.pow k k := by
  rfl

theorem toNat_succ_eq_nat_pow_term (n : Nat) :
    toNat (Nat.succ n) = toNat n * Nat.pow (Nat.succ n) (Nat.succ n) := by
  rw [toNat_succ, hyperfactorialTerm_eq_nat_pow]

theorem hyperfactorial_succ_eq_nat_pow_term
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.HyperfactorialUp.hyperfactorial (Nat.succ n) =
      BEDC.Derived.HyperfactorialUp.hyperfactorial n *
        Nat.pow (Nat.succ n) (Nat.succ n) := by
  change toNat (Nat.succ n) = toNat n * Nat.pow (Nat.succ n) (Nat.succ n)
  exact toNat_succ_eq_nat_pow_term n

end BedcMathlibBridge.Constructive.Hyperfactorial
