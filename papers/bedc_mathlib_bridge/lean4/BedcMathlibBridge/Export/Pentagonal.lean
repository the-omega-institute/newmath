import BedcMathlibBridge.Constructive.Pentagonal

/-!
Export witness for the pentagonal number structural correspondence.

The witness records that the readback is the BEDC pentagonal number
`BEDC.Derived.PolygonalUp.pentagonalNumber`, satisfies both boundaries and the
BEDC recurrence `P (n+1) = P n + (3*n + 1)`, and is pointwise equal to mathlib's
`3 * Nat.choose n 2 + n`.
-/

namespace BedcMathlibBridge.Export.Pentagonal

open BedcMathlibBridge.Constructive.Pentagonal

structure PentagonalExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PolygonalUp.pentagonalNumber n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat, readback (Nat.succ n) = readback n + (3 * n + 1)
  nat_choose_apply : ∀ n : Nat, readback n = 3 * Nat.choose n 2 + n

def pentagonalExport : PentagonalExportWitness where
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

theorem pentagonalNumber_eq_nat_choose (n : Nat) :
    BEDC.Derived.PolygonalUp.pentagonalNumber n = 3 * Nat.choose n 2 + n :=
  BedcMathlibBridge.Constructive.Pentagonal.toNat_eq_nat_choose n

end BedcMathlibBridge.Export.Pentagonal
