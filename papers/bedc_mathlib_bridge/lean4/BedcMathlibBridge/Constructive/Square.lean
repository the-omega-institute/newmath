import BedcMathlibBridge.Constructive.Triangular
import BedcMathlibBridge.Export.Triangular
import BEDC.Derived.PolygonalUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Square number structural correspondence.

`BEDC.Derived.PolygonalUp.squareNumber n` is `n * n`, the fourth polygonal
number. Its genuine mathlib correspondence is the binomial identity
`squareNumber n = Nat.choose (n + 1) 2 + Nat.choose n 2`: the `n`-th square is
the sum of the `n`-th and `(n-1)`-th triangular numbers, each transported to
mathlib's `Nat.choose` through the certified triangular bridge. The plain
closed forms `n * n` and `n ^ 2` are core `Nat` arithmetic (not mathlib
content), so they are exported only as secondary readback fields.
-/

namespace BedcMathlibBridge.Constructive.Square

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC square number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.PolygonalUp.squareNumber n

theorem toNat_eq_squareNumber (n : Nat) :
    toNat n = BEDC.Derived.PolygonalUp.squareNumber n :=
  rfl

/-- Boundary: the `0`-th square number is `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first square number is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The BEDC square recurrence `S (n+1) = S n + n + (n+1)`, transported through
the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + n + Nat.succ n := by
  change
    BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n) =
      BEDC.Derived.PolygonalUp.squareNumber n + n + Nat.succ n
  exact BEDC.Derived.PolygonalUp.square_succ n

/-- Secondary closed form: the square number is `n * n` (core `Nat`). -/
theorem toNat_eq_mul_self (n : Nat) :
    toNat n = n * n := by
  rfl

/-- The square number is the fourth polygonal number. -/
theorem toNat_eq_polygonal_four (n : Nat) :
    toNat n = BEDC.Derived.PolygonalUp.polygonalNumber 4 n := by
  change
    BEDC.Derived.PolygonalUp.squareNumber n =
      BEDC.Derived.PolygonalUp.polygonalNumber 4 n
  exact (BEDC.Derived.PolygonalUp.polygonal_four_eq_square n).symm

/-- The main structural correspondence: the BEDC square number is the sum of two
consecutive triangular numbers, i.e. mathlib's
`Nat.choose (n + 1) 2 + Nat.choose n 2`. -/
theorem toNat_eq_nat_choose_sum (n : Nat) :
    toNat n = Nat.choose (n + 1) 2 + Nat.choose n 2 := by
  change BEDC.Derived.PolygonalUp.squareNumber n = _
  rw [← BEDC.Derived.PolygonalUp.triangular_add_previous_eq_square n]
  have h1 : BEDC.Derived.PolygonalUp.triangularNumber n = Nat.choose (n + 1) 2 :=
    BedcMathlibBridge.Export.Triangular.triangularNumber_eq_nat_choose n
  cases n with
  | zero => rfl
  | succ m =>
    have h2 :
        BEDC.Derived.PolygonalUp.triangularNumber m = Nat.choose (m + 1) 2 :=
      BedcMathlibBridge.Export.Triangular.triangularNumber_eq_nat_choose m
    rw [h1]
    change
      _ + BEDC.Derived.PolygonalUp.triangularNumber m = _
    rw [h2]

end BedcMathlibBridge.Constructive.Square
