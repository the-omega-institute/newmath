import BedcMathlibBridge.Constructive.Factorial
import BEDC.Derived.QFactorialUp
import Mathlib.Data.Nat.Factorial.Basic

/-!
q-factorial structural correspondence.

`BEDC.Derived.QFactorialUp.qFactorial n : List Nat` is the BEDC q-factorial
polynomial represented by exponent rows. This module only bridges its `q = 1`
readback: `polyEvalOne` collapses the polynomial to the coefficient count, and
that count is mathlib's `Nat.factorial`.
-/

namespace BedcMathlibBridge.Constructive.QFactorial

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

/-- q=1 evaluation of the BEDC q-factorial polynomial. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.QFactorialUp.polyEvalOne
    (BEDC.Derived.QFactorialUp.qFactorial n)

theorem toNat_eq_qFactorial_evalOne (n : Nat) :
    toNat n =
      BEDC.Derived.QFactorialUp.polyEvalOne
        (BEDC.Derived.QFactorialUp.qFactorial n) :=
  rfl

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ_mul (n : Nat) :
    toNat (Nat.succ n) = Nat.succ n * toNat n := by
  calc
    toNat (Nat.succ n) =
        BEDC.Derived.QFactorialUp.factorialNat (Nat.succ n) :=
      BEDC.Derived.QFactorialUp.qFactorial_evalOne_factorialNat (Nat.succ n)
    _ = BEDC.Derived.QFactorialUp.factorialNat n * Nat.succ n := by
      exact BEDC.Derived.PochhammerUp.natFactorialCount_succ n
    _ = toNat n * Nat.succ n := by
      exact congrArg (fun x => x * Nat.succ n)
        (BEDC.Derived.QFactorialUp.qFactorial_evalOne_factorialNat n).symm
    _ = Nat.succ n * toNat n := Nat.mul_comm (toNat n) (Nat.succ n)

theorem factorialNat_eq_nat_factorial (n : Nat) :
    BEDC.Derived.QFactorialUp.factorialNat n = Nat.factorial n := by
  change BedcMathlibBridge.Constructive.Factorial.toNat n = Nat.factorial n
  exact BedcMathlibBridge.Constructive.Factorial.toNat_eq_nat_factorial n

/-- The main structural correspondence: the BEDC q-factorial polynomial,
evaluated at `q = 1`, equals mathlib's `Nat.factorial`. -/
theorem toNat_eq_nat_factorial (n : Nat) : toNat n = Nat.factorial n := by
  calc
    toNat n = BEDC.Derived.QFactorialUp.factorialNat n :=
      BEDC.Derived.QFactorialUp.qFactorial_evalOne_factorialNat n
    _ = Nat.factorial n := factorialNat_eq_nat_factorial n

end BedcMathlibBridge.Constructive.QFactorial
