import BEDC.Derived.EulerianNumberUp
import BedcMathlibBridge.Constructive.Factorial
import Mathlib.Data.Nat.Factorial.Basic

/-!
Eulerian row-sum structural correspondence.

The bridge surface is only the row sum of the BEDC Eulerian-number recurrence.
BEDC proves that this row sum is its factorial counter, and the existing
factorial bridge identifies that counter with mathlib `Nat.factorial`.
-/

namespace BedcMathlibBridge.Constructive.Eulerian

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

/-- Direct Nat readback of the BEDC Eulerian row sum. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.EulerianNumberUp.eulerianRowSum n

theorem toNat_eq_eulerianRowSum (n : Nat) :
    toNat n = BEDC.Derived.EulerianNumberUp.eulerianRowSum n :=
  rfl

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ_mul (n : Nat) :
    toNat (Nat.succ n) = Nat.succ n * toNat n := by
  exact BEDC.Derived.EulerianNumberUp.eulerianRowSum_succ n

/-- The main structural correspondence: the BEDC Eulerian row sum equals
mathlib's `Nat.factorial`. -/
theorem toNat_eq_nat_factorial (n : Nat) : toNat n = Nat.factorial n := by
  calc
    toNat n = BEDC.Derived.PochhammerUp.natFactorialCount n :=
      BEDC.Derived.EulerianNumberUp.eulerianRowSum_eq_natFactorialCount n
    _ = Nat.factorial n := by
      change BedcMathlibBridge.Constructive.Factorial.toNat n = Nat.factorial n
      exact BedcMathlibBridge.Constructive.Factorial.toNat_eq_nat_factorial n

end BedcMathlibBridge.Constructive.Eulerian
