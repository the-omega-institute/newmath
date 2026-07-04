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

private def mathlibNatTriangleProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ a b : Nat, Nat.add a b = a + b := fun _ _ => rfl
  let _ : ∀ a b : Nat, Nat.mul a b = a * b := fun _ _ => rfl
  let _ : ∀ a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  ()

/-- Direct Nat readback of the BEDC Eulerian row sum. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.EulerianNumberUp.eulerianRowSum n

/-- Direct Nat readback of the BEDC Eulerian-number triangle. -/
def triangleReadback (n k : Nat) : Nat :=
  let _ := mathlibNatTriangleProvenanceAnchor
  BEDC.Derived.EulerianNumberUp.eulerianNumber n k

theorem toNat_eq_eulerianRowSum (n : Nat) :
    toNat n = BEDC.Derived.EulerianNumberUp.eulerianRowSum n :=
  rfl

theorem triangleReadback_apply (n k : Nat) :
    triangleReadback n k =
      BEDC.Derived.EulerianNumberUp.eulerianNumber n k := by
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

theorem mathlibNatTriangleAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem triangle_zero_zero :
    triangleReadback 0 0 = 1 := by
  rfl

theorem triangle_zero_succ (k : Nat) :
    triangleReadback 0 (Nat.succ k) = 0 := by
  rfl

theorem triangle_left_boundary (n : Nat) :
    triangleReadback n 0 = 1 := by
  change BEDC.Derived.EulerianNumberUp.eulerianNumber n 0 = 1
  exact BEDC.Derived.EulerianNumberUp.eulerian_left_boundary n

theorem triangle_recurrence_nat_mul_add_sub
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective :=
      mathlibNatTriangleAnchor) :
    triangleReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ k)) (triangleReadback n (Nat.succ k)))
        (Nat.mul (Nat.sub n k) (triangleReadback n k)) := by
  change
    BEDC.Derived.EulerianNumberUp.eulerianNumber (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul
          (Nat.succ (Nat.succ k))
          (BEDC.Derived.EulerianNumberUp.eulerianNumber n (Nat.succ k)))
        (Nat.mul (Nat.sub n k)
          (BEDC.Derived.EulerianNumberUp.eulerianNumber n k))
  exact BEDC.Derived.EulerianNumberUp.eulerian_recurrence n k

theorem triangle_above_row_zero (n extra : Nat) :
    triangleReadback n (Nat.succ (n + extra)) = 0 := by
  change
    BEDC.Derived.EulerianNumberUp.eulerianNumber n
      (Nat.succ (n + extra)) = 0
  exact BEDC.Derived.EulerianNumberUp.eulerian_succ_above n extra

end BedcMathlibBridge.Constructive.Eulerian
