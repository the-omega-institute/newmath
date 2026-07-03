import BEDC.Derived.EuclidFactorialNumberUp
import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.EuclidFactorial

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.EuclidFactorialNumberUp.euclidFactorialNumber n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.EuclidFactorialNumberUp.euclidFactorialNumber n := by
  rfl

theorem toNat_zero : toNat 0 = 2 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) =
      Nat.succ n * BEDC.Derived.EuclidFactorialNumberUp.factorialNat n + 1 := by
  rfl

theorem factorialNat_eq_nat_factorial (n : Nat) :
    BEDC.Derived.EuclidFactorialNumberUp.factorialNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [BEDC.Derived.EuclidFactorialNumberUp.factorialNat_succ, ih]
      rfl

theorem toNat_eq_nat_factorial_add_one (n : Nat) :
    toNat n = Nat.factorial n + 1 := by
  unfold toNat BEDC.Derived.EuclidFactorialNumberUp.euclidFactorialNumber
  rw [factorialNat_eq_nat_factorial]

end BedcMathlibBridge.Constructive.EuclidFactorial
