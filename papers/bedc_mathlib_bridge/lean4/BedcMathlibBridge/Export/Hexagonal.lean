import BedcMathlibBridge.Constructive.Hexagonal

/-!
Export witness for the hexagonal number structural correspondence.

The witness records that the readback is the BEDC hexagonal number
`BEDC.Derived.PolygonalUp.polygonalNumber 6`, satisfies both boundaries and the
BEDC recurrence `P (n+1) = P n + (4*n + 1)`, and is pointwise equal to mathlib's
`4 * Nat.choose n 2 + n`.
-/

namespace BedcMathlibBridge.Export.Hexagonal

open BedcMathlibBridge.Constructive.Hexagonal

structure HexagonalExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PolygonalUp.polygonalNumber 6 n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat, readback (Nat.succ n) = readback n + (4 * n + 1)
  nat_choose_apply : ∀ n : Nat, readback n = 4 * Nat.choose n 2 + n

def hexagonalExport : HexagonalExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  one_apply := toNat_one
  succ_apply := toNat_succ
  nat_choose_apply := toNat_eq_nat_choose

theorem polygonalNumber_six_eq_nat_choose (n : Nat) :
    BEDC.Derived.PolygonalUp.polygonalNumber 6 n = 4 * Nat.choose n 2 + n :=
  BedcMathlibBridge.Constructive.Hexagonal.toNat_eq_nat_choose n

end BedcMathlibBridge.Export.Hexagonal
