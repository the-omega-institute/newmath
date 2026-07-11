import BEDC.Derived.StirlingCycleUp
import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.StirlingCycleColumn

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.StirlingCycleUp.stirlingCycle (Nat.succ n) 1

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = Nat.succ n * toNat n := by
  unfold toNat
  rw [BEDC.Derived.StirlingCycleUp.stirlingCycle_recurrence (Nat.succ n) 0]
  rw [BEDC.Derived.StirlingCycleUp.stirlingCycle_succ_zero n]
  rw [Nat.add_zero]

theorem toNat_eq_nat_factorial (n : Nat) :
    toNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        toNat (Nat.succ n) = Nat.succ n * toNat n := toNat_succ n
        _ = Nat.succ n * Nat.factorial n := by
          rw [ih]
        _ = Nat.factorial (Nat.succ n) := by
          rfl

end BedcMathlibBridge.Constructive.StirlingCycleColumn
