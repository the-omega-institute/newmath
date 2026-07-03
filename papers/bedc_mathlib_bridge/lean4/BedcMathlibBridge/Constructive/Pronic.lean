import BedcMathlibBridge.Constructive.Triangular
import BedcMathlibBridge.Export.Triangular
import BEDC.Derived.PronicNumberUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Pronic (oblong) number structural correspondence.

`BEDC.Derived.PronicNumberUp.pronicNumber n` is `n * (n + 1)`, the `n`-th
oblong number. BEDC verifies `pronicNumber n = 2 * triangularNumber n` and, via
the already-certified triangular bridge, the readback transports to mathlib's
`2 * Nat.choose (n + 1) 2` (twice the `n`-th triangular number in mathlib's
binomial presentation). BEDC further certifies that a positive pronic number is
never a perfect square; that squeeze fact is exported alongside the value
correspondence.
-/

namespace BedcMathlibBridge.Constructive.Pronic

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC pronic number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.PronicNumberUp.pronicNumber n

theorem toNat_eq_pronicNumber (n : Nat) :
    toNat n = BEDC.Derived.PronicNumberUp.pronicNumber n :=
  rfl

/-- Closed form: the pronic number is `n * (n + 1)`. -/
theorem toNat_eq_mul_succ (n : Nat) :
    toNat n = n * (n + 1) := by
  rfl

/-- Boundary: the `0`-th pronic number is `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first pronic number is `2`. -/
theorem toNat_one : toNat 1 = 2 := by
  rfl

/-- The pronic number is twice the corresponding BEDC triangular number. -/
theorem toNat_eq_two_mul_triangular (n : Nat) :
    toNat n = 2 * BEDC.Derived.PolygonalUp.triangularNumber n := by
  change
    BEDC.Derived.PronicNumberUp.pronicNumber n =
      2 * BEDC.Derived.PolygonalUp.triangularNumber n
  exact BEDC.Derived.PronicNumberUp.pronic_eq_two_mul_triangular n

/-- The main structural correspondence: the BEDC pronic number equals mathlib's
`2 * Nat.choose (n + 1) 2`. -/
theorem toNat_eq_two_mul_nat_choose (n : Nat) :
    toNat n = 2 * Nat.choose (n + 1) 2 := by
  rw [toNat_eq_two_mul_triangular n]
  have h : BEDC.Derived.PolygonalUp.triangularNumber n = Nat.choose (n + 1) 2 :=
    BedcMathlibBridge.Export.Triangular.triangularNumber_eq_nat_choose n
  exact congrArg (fun t => 2 * t) h

/-- A positive pronic number is never a perfect square (BEDC squeeze between
consecutive squares). -/
theorem pronic_not_perfect_square_of_pos (n : Nat) :
    0 < n -> BEDC.Derived.PronicNumberUp.IsPerfectSquare (toNat n) -> False :=
  BEDC.Derived.PronicNumberUp.pronic_not_perfect_square_of_pos n

end BedcMathlibBridge.Constructive.Pronic
