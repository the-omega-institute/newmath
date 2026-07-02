import BedcMathlibBridge.Constructive.Triangular
import BedcMathlibBridge.Export.Triangular
import BEDC.Derived.CenteredPolygonalUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Centered hexagonal number structural correspondence.

`BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber n` is
`6 * chooseTwo n + 1`, where `chooseTwo n = n * (n - 1) / 2`. BEDC certifies the
`chooseTwo` presentation through the triangular binomial-row identity, so the
readback transports to mathlib's `6 * Nat.choose n 2 + 1`.

The bridge lemma `chooseTwo_eq_nat_choose` (`chooseTwo m = Nat.choose m 2`) is a
reusable centered-polygonal transport: `centeredHexagonalNumber` is the `k = 6`
instance, and the same lemma also gives the centered triangular (`k = 3`) and
centered square (`k = 4`) correspondences.
-/

namespace BedcMathlibBridge.Constructive.CenteredHexagonal

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- `chooseTwo m = Nat.choose m 2`, transported from the certified triangular
bridge (`triangularNumber n = chooseTwo (n + 1) = Nat.choose (n + 1) 2`). -/
theorem chooseTwo_eq_nat_choose (m : Nat) :
    BEDC.Derived.StirlingUp.chooseTwo m = Nat.choose m 2 := by
  cases m with
  | zero => rfl
  | succ n =>
    change BEDC.Derived.PolygonalUp.triangularNumber n = Nat.choose (Nat.succ n) 2
    exact BedcMathlibBridge.Export.Triangular.triangularNumber_eq_nat_choose n

/-- Direct `Nat` readback of the BEDC centered hexagonal number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber n

theorem toNat_eq_centeredHexagonalNumber (n : Nat) :
    toNat n = BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber n :=
  rfl

/-- Boundary: the `0`-th centered hexagonal number is `1` (the central dot). -/
theorem toNat_zero : toNat 0 = 1 := by
  rfl

/-- The first centered hexagonal number (index `1`) is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The centered hexagonal number at index `2` is `7` (first hexagonal ring). -/
theorem toNat_two : toNat 2 = 7 := by
  rfl

/-- The BEDC closed form `H_c n = 6 * chooseTwo n + 1`. -/
theorem toNat_eq_six_mul_chooseTwo (n : Nat) :
    toNat n = 6 * BEDC.Derived.StirlingUp.chooseTwo n + 1 := by
  change
    BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber n =
      6 * BEDC.Derived.StirlingUp.chooseTwo n + 1
  exact BEDC.Derived.CenteredPolygonalUp.centeredHexagonal_formula n

/-- The main structural correspondence: the BEDC centered hexagonal number
equals mathlib's `6 * Nat.choose n 2 + 1`. -/
theorem toNat_eq_nat_choose (n : Nat) :
    toNat n = 6 * Nat.choose n 2 + 1 := by
  rw [toNat_eq_six_mul_chooseTwo n, chooseTwo_eq_nat_choose n]

/-- Centered triangular number `= 3 * Nat.choose n 2 + 1` (same transport). -/
theorem centeredTriangular_eq_nat_choose (n : Nat) :
    BEDC.Derived.CenteredPolygonalUp.centeredTriangularNumber n
      = 3 * Nat.choose n 2 + 1 := by
  have h : BEDC.Derived.CenteredPolygonalUp.centeredTriangularNumber n
      = 3 * BEDC.Derived.StirlingUp.chooseTwo n + 1 :=
    BEDC.Derived.CenteredPolygonalUp.centeredTriangular_formula n
  rw [h, chooseTwo_eq_nat_choose n]

/-- Centered square number `= 4 * Nat.choose n 2 + 1` (same transport). -/
theorem centeredSquare_eq_nat_choose (n : Nat) :
    BEDC.Derived.CenteredPolygonalUp.centeredSquareNumber n
      = 4 * Nat.choose n 2 + 1 := by
  have h : BEDC.Derived.CenteredPolygonalUp.centeredSquareNumber n
      = 4 * BEDC.Derived.StirlingUp.chooseTwo n + 1 :=
    BEDC.Derived.CenteredPolygonalUp.centeredSquare_formula n
  rw [h, chooseTwo_eq_nat_choose n]

end BedcMathlibBridge.Constructive.CenteredHexagonal
