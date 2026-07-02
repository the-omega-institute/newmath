import BEDC.Derived.StirlingCycleUp
import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.AscFactorial

private def mathlibAscFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.ascFactorial n k = Nat.ascFactorial n k :=
    fun _ _ => rfl
  ()

def toNat (x k : Nat) : Nat :=
  let _ := mathlibAscFactorialProvenanceAnchor
  BEDC.Derived.StirlingCycleUp.risingFactorialValue x k

theorem toNat_zero (x : Nat) : toNat x 0 = 1 := by
  rfl

theorem toNat_succ (x k : Nat) :
    toNat x (Nat.succ k) = toNat x k * (x + k) := by
  rfl

theorem toNat_eq_ascFactorial (x k : Nat) :
    toNat x k = Nat.ascFactorial x k := by
  induction k with
  | zero =>
      rw [toNat_zero, Nat.ascFactorial_zero]
  | succ k ih =>
      rw [toNat_succ, ih, Nat.ascFactorial_succ, Nat.mul_comm]

end BedcMathlibBridge.Constructive.AscFactorial
