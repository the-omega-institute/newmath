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
  let _ : ∀ n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def firstColumnToNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1

theorem firstColumnToNat_apply (n : Nat) :
    firstColumnToNat n = BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 := by
  rfl

theorem firstColumnToNat_eq_bedc_factorialNat (n : Nat) :
    firstColumnToNat n =
      BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) := by
  change BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 =
    BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n)
  exact BEDC.Derived.LahUp.lahNumber_succ_one_eq_factorial n

theorem factorialNat_eq_nat_factorial (n : Nat) :
    BEDC.Derived.StirlingFirstUp.factorialNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Nat.succ n * BEDC.Derived.StirlingFirstUp.factorialNat n =
        Nat.factorial (Nat.succ n)
      rw [ih, Nat.factorial_succ]

theorem firstColumnToNat_eq_nat_factorial_succ (n : Nat) :
    firstColumnToNat n = Nat.factorial (Nat.succ n) := by
  calc
    firstColumnToNat n =
        BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) :=
      firstColumnToNat_eq_bedc_factorialNat n
    _ = Nat.factorial (Nat.succ n) :=
      factorialNat_eq_nat_factorial (Nat.succ n)

theorem firstColumnToNat_succ_recurrence_mathlib (n : Nat) :
    firstColumnToNat (Nat.succ n) =
      Nat.succ (Nat.succ n) * firstColumnToNat n := by
  calc
    firstColumnToNat (Nat.succ n) =
        Nat.factorial (Nat.succ (Nat.succ n)) :=
      firstColumnToNat_eq_nat_factorial_succ (Nat.succ n)
    _ = Nat.succ (Nat.succ n) * Nat.factorial (Nat.succ n) := by
      rw [Nat.factorial_succ]
    _ = Nat.succ (Nat.succ n) * firstColumnToNat n := by
      rw [firstColumnToNat_eq_nat_factorial_succ n]

def toNat (n : Nat) : Nat :=
  firstColumnToNat n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 :=
  firstColumnToNat_apply n

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_eq_stirling_factorial_succ (n : Nat) :
    toNat n = BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) :=
  firstColumnToNat_eq_bedc_factorialNat n

theorem toNat_eq_nat_factorial_succ (n : Nat) :
    toNat n = Nat.factorial (Nat.succ n) :=
  firstColumnToNat_eq_nat_factorial_succ n

end BedcMathlibBridge.Constructive.Lah
