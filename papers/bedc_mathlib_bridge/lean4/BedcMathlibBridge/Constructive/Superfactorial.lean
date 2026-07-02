import BEDC.Derived.HyperfactorialUp
import Mathlib.Data.Nat.Factorial.SuperFactorial

namespace BedcMathlibBridge.Constructive.Superfactorial

private def mathlibSuperFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.superFactorial n = Nat.superFactorial n :=
    fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibSuperFactorialProvenanceAnchor
  BEDC.Derived.HyperfactorialUp.superfactorial n

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) =
      toNat n * BEDC.Derived.HyperfactorialUp.factorialNat (Nat.succ n) := by
  rfl

/-- The BEDC hyperfactorial-file factorial agrees with `Nat.factorial`; both are
the same structural recursion. -/
theorem factorialNat_eq_factorial (n : Nat) :
    BEDC.Derived.HyperfactorialUp.factorialNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [BEDC.Derived.HyperfactorialUp.factorialNat_succ, ih, Nat.factorial_succ]

theorem toNat_eq_superFactorial (n : Nat) :
    toNat n = Nat.superFactorial n := by
  induction n with
  | zero =>
      rw [toNat_zero, Nat.superFactorial_zero]
  | succ n ih =>
      rw [toNat_succ, ih, factorialNat_eq_factorial, Nat.superFactorial_succ,
        Nat.mul_comm]

end BedcMathlibBridge.Constructive.Superfactorial
