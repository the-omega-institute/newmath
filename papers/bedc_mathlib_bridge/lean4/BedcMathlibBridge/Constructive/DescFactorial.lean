import BEDC.Derived.StirlingSecondCompleteUp
import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.DescFactorial

private def mathlibDescFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.descFactorial n k = Nat.descFactorial n k :=
    fun _ _ => rfl
  ()

def toNat (x k : Nat) : Nat :=
  let _ := mathlibDescFactorialProvenanceAnchor
  BEDC.Derived.StirlingSecondCompleteUp.fallingFactorial x k

theorem toNat_zero (x : Nat) : toNat x 0 = 1 := by
  rfl

theorem toNat_succ (x k : Nat) :
    toNat x (Nat.succ k) = toNat x k * (x - k) := by
  rfl

theorem toNat_eq_descFactorial (x k : Nat) :
    toNat x k = Nat.descFactorial x k := by
  induction k with
  | zero =>
      rw [toNat_zero, Nat.descFactorial_zero]
  | succ k ih =>
      rw [toNat_succ, ih, Nat.descFactorial_succ, Nat.mul_comm]

end BedcMathlibBridge.Constructive.DescFactorial
