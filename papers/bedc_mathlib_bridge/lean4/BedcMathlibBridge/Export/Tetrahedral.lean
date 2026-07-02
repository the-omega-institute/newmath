import BedcMathlibBridge.Constructive.Tetrahedral

/-!
Export witness for the tetrahedral number structural correspondence.

The witness records that the readback is the BEDC tetrahedral number
`BEDC.Derived.TetrahedralUp.tetrahedralNumber`, satisfies both boundaries and
the BEDC tetrahedral recurrence, and is pointwise equal to mathlib's
`Nat.choose (n + 2) 3`.
-/

namespace BedcMathlibBridge.Export.Tetrahedral

open BedcMathlibBridge.Constructive.Tetrahedral

structure TetrahedralExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.TetrahedralUp.tetrahedralNumber n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat,
    readback (Nat.succ n) =
      readback n + BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n)
  nat_choose_apply : ∀ n : Nat, readback n = Nat.choose (n + 2) 3

def tetrahedralExport : TetrahedralExportWitness where
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

theorem tetrahedralNumber_eq_nat_choose (n : Nat) :
    BEDC.Derived.TetrahedralUp.tetrahedralNumber n = Nat.choose (n + 2) 3 :=
  BedcMathlibBridge.Constructive.Tetrahedral.toNat_eq_nat_choose n

end BedcMathlibBridge.Export.Tetrahedral
