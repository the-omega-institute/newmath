import BEDC.Derived.LahNumberUp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
Lah diagonal closed-form slice.

The BEDC side already carries the Lah recurrence and exact closed-division
surface. This bridge exposes the diagonal row against the standard
`Nat.choose`/`Nat.factorial` expression without importing a host Lah API.
-/

namespace BedcMathlibBridge.Constructive.LahClosedForm

private def mathlibChooseFactorialProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def diagonalReadback (n : Nat) : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ n)

def diagonalClosedNumeratorReadback (n : Nat) : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahClosedNumerator (Nat.succ n) (Nat.succ n)

def diagonalClosedDenominatorReadback (n : Nat) : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahClosedDenominator (Nat.succ n)

def mathlibDiagonalNumerator (n : Nat) : Nat :=
  Nat.choose n n * Nat.factorial (Nat.succ n)

def mathlibDiagonalDenominator (n : Nat) : Nat :=
  Nat.factorial (Nat.succ n)

theorem factorialNat_eq_nat_factorial (n : Nat) :
    BEDC.Derived.LahNumberUp.factorialNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        BEDC.Derived.LahNumberUp.factorialNat (Nat.succ n) =
            Nat.succ n * BEDC.Derived.LahNumberUp.factorialNat n := by
          rfl
        _ = Nat.succ n * Nat.factorial n := by
          rw [ih]
        _ = Nat.factorial (Nat.succ n) := by
          rfl

theorem nat_choose_self (n : Nat) :
    Nat.choose n n = 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Nat.choose (Nat.succ n) (Nat.succ n) = 1
      rw [Nat.choose_succ_succ]
      rw [ih]
      rw [Nat.choose_succ_self]

theorem diagonalReadback_apply (n : Nat) :
    diagonalReadback n =
      BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ n) := by
  rfl

theorem diagonal_eq_one (n : Nat) :
    diagonalReadback n = 1 := by
  unfold diagonalReadback
  exact BEDC.Derived.LahNumberUp.lahNumber_self (Nat.succ n)

theorem diagonal_closed_numerator_eq_mathlib (n : Nat) :
    diagonalClosedNumeratorReadback n = mathlibDiagonalNumerator n := by
  unfold diagonalClosedNumeratorReadback mathlibDiagonalNumerator
  unfold BEDC.Derived.LahNumberUp.lahClosedNumerator
  unfold BEDC.Derived.LahNumberUp.C
  change
    BEDC.Derived.BinomialIdentitiesUp.C n n *
        BEDC.Derived.LahNumberUp.factorialNat (Nat.succ n) =
      Nat.choose n n * Nat.factorial (Nat.succ n)
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self]
  rw [nat_choose_self]
  rw [factorialNat_eq_nat_factorial]

theorem diagonal_closed_denominator_eq_mathlib (n : Nat) :
    diagonalClosedDenominatorReadback n = mathlibDiagonalDenominator n := by
  unfold diagonalClosedDenominatorReadback mathlibDiagonalDenominator
  unfold BEDC.Derived.LahNumberUp.lahClosedDenominator
  exact factorialNat_eq_nat_factorial (Nat.succ n)

theorem diagonal_exact_closed_division (n : Nat) :
    diagonalReadback n * diagonalClosedDenominatorReadback n =
      diagonalClosedNumeratorReadback n := by
  have h :=
    BEDC.Derived.LahNumberUp.lahExactClosedDivision_diagonal n
  exact h

theorem diagonal_mathlib_closed_division (n : Nat) :
    diagonalReadback n * mathlibDiagonalDenominator n =
      mathlibDiagonalNumerator n := by
  calc
    diagonalReadback n * mathlibDiagonalDenominator n =
        diagonalReadback n * diagonalClosedDenominatorReadback n := by
      rw [diagonal_closed_denominator_eq_mathlib]
    _ = diagonalClosedNumeratorReadback n :=
      diagonal_exact_closed_division n
    _ = mathlibDiagonalNumerator n :=
      diagonal_closed_numerator_eq_mathlib n

end BedcMathlibBridge.Constructive.LahClosedForm
