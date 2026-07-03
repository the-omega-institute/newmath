import BEDC.Derived.JacobsthalUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.PowTwo

private def mathlibPowProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.pow 2 n = Nat.pow 2 n := fun _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibPowProvenanceAnchor
  BEDC.Derived.JacobsthalUp.powTwo n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.JacobsthalUp.powTwo n := by
  rfl

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (n + 1) = 2 * toNat n := by
  rfl

theorem mathlibPowAnchor : Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_eq_nat_pow_two (n : Nat) :
    toNat n = Nat.pow 2 n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        toNat (Nat.succ n) = 2 * toNat n := toNat_succ n
        _ = 2 * Nat.pow 2 n := by
          rw [ih]
        _ = Nat.pow 2 n * 2 := Nat.mul_comm 2 (Nat.pow 2 n)
        _ = Nat.pow 2 (Nat.succ n) := (Nat.pow_succ 2 n).symm

end BedcMathlibBridge.Constructive.PowTwo
