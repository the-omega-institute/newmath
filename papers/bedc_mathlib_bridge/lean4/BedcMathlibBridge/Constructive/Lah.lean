import BEDC.Derived.LahUp
import Mathlib.Data.Nat.Factorial.Basic

/-!
Lah first-column structural correspondence.

`BEDC.Derived.LahUp.lahNumber (n+1) 1` is the BEDC Lah first column. The
bridge records only the checked first-column factorial slice, not a host Lah
number API.
-/

namespace BedcMathlibBridge.Constructive.Lah

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 := by
  rfl

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_eq_stirling_factorial_succ (n : Nat) :
    toNat n = BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) := by
  change
    BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 =
      BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n)
  exact BEDC.Derived.LahUp.lahNumber_succ_one_eq_factorial n

private theorem stirlingFirstFactorialNat_eq_nat_factorial (n : Nat) :
    BEDC.Derived.StirlingFirstUp.factorialNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) =
            Nat.succ n * BEDC.Derived.StirlingFirstUp.factorialNat n := by
          rfl
        _ = Nat.succ n * Nat.factorial n := by
          rw [ih]
        _ = Nat.factorial (Nat.succ n) := by
          rfl

theorem toNat_eq_nat_factorial_succ (n : Nat) :
    toNat n = Nat.factorial (Nat.succ n) := by
  calc
    toNat n = BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) :=
      toNat_eq_stirling_factorial_succ n
    _ = Nat.factorial (Nat.succ n) :=
      stirlingFirstFactorialNat_eq_nat_factorial (Nat.succ n)

end BedcMathlibBridge.Constructive.Lah
