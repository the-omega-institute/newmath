import BedcMathlibBridge.Constructive.Triangular

/-!
Export witness for the triangular number structural correspondence.

The witness records that the readback is the BEDC triangular number
`BEDC.Derived.PolygonalUp.triangularNumber`, satisfies both boundaries and the
BEDC triangular recurrence, and is pointwise equal to mathlib's
`Nat.choose (n + 1) 2`.
-/

namespace BedcMathlibBridge.Export.Triangular

open BedcMathlibBridge.Constructive.Triangular

structure TriangularExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PolygonalUp.triangularNumber n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat, readback (Nat.succ n) = readback n + Nat.succ n
  nat_choose_apply : ∀ n : Nat, readback n = Nat.choose (n + 1) 2

def triangularExport : TriangularExportWitness where
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

theorem triangularNumber_eq_nat_choose (n : Nat) :
    BEDC.Derived.PolygonalUp.triangularNumber n = Nat.choose (n + 1) 2 :=
  BedcMathlibBridge.Constructive.Triangular.toNat_eq_nat_choose n

end BedcMathlibBridge.Export.Triangular
