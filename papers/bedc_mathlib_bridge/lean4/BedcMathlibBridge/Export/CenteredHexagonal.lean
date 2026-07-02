import BedcMathlibBridge.Constructive.CenteredHexagonal

/-!
Export witness for the centered hexagonal number structural correspondence.

The witness records that the readback is the BEDC centered hexagonal number
`BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber`, satisfies both
boundaries, has BEDC closed form `6 * chooseTwo n + 1`, and is pointwise equal
to mathlib's `6 * Nat.choose n 2 + 1`. The `chooseTwo = Nat.choose · 2`
transport is shared with the centered triangular (`k = 3`) and centered square
(`k = 4`) correspondences, which are recorded as additional witness fields.
-/

namespace BedcMathlibBridge.Export.CenteredHexagonal

open BedcMathlibBridge.Constructive.CenteredHexagonal

structure CenteredHexagonalExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 1
  two_apply : readback 2 = 7
  six_chooseTwo_apply : ∀ n : Nat,
    readback n = 6 * BEDC.Derived.StirlingUp.chooseTwo n + 1
  nat_choose_apply : ∀ n : Nat, readback n = 6 * Nat.choose n 2 + 1
  centered_triangular_apply : ∀ n : Nat,
    BEDC.Derived.CenteredPolygonalUp.centeredTriangularNumber n
      = 3 * Nat.choose n 2 + 1
  centered_square_apply : ∀ n : Nat,
    BEDC.Derived.CenteredPolygonalUp.centeredSquareNumber n
      = 4 * Nat.choose n 2 + 1

def centeredHexagonalExport : CenteredHexagonalExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  one_apply := toNat_one
  two_apply := toNat_two
  six_chooseTwo_apply := toNat_eq_six_mul_chooseTwo
  nat_choose_apply := toNat_eq_nat_choose
  centered_triangular_apply := centeredTriangular_eq_nat_choose
  centered_square_apply := centeredSquare_eq_nat_choose

theorem centeredHexagonalNumber_eq_nat_choose (n : Nat) :
    BEDC.Derived.CenteredPolygonalUp.centeredHexagonalNumber n
      = 6 * Nat.choose n 2 + 1 :=
  BedcMathlibBridge.Constructive.CenteredHexagonal.toNat_eq_nat_choose n

end BedcMathlibBridge.Export.CenteredHexagonal
