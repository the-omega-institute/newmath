import BedcMathlibBridge.Constructive.PolygonalNumberTriangular

/-!
Export witness for the `PolygonalNumberUp` triangular number correspondence.

The witness records a direct `Nat` readback of
`BEDC.Derived.PolygonalNumberUp.triangularNumber`, its BEDC recurrence, and the
pointwise equality with mathlib's `Nat.choose (n + 1) 2`.
-/

namespace BedcMathlibBridge.Export.PolygonalNumberTriangular

open BedcMathlibBridge.Constructive.PolygonalNumberTriangular

structure PolygonalNumberTriangularExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PolygonalNumberUp.triangularNumber n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat, readback (Nat.succ n) = readback n + Nat.succ n
  nat_choose_apply : ∀ n : Nat, readback n = Nat.choose (n + 1) 2

def polygonalNumberTriangularExport : PolygonalNumberTriangularExportWitness where
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
    BEDC.Derived.PolygonalNumberUp.triangularNumber n = Nat.choose (n + 1) 2 :=
  BedcMathlibBridge.Constructive.PolygonalNumberTriangular.toNat_eq_nat_choose n

end BedcMathlibBridge.Export.PolygonalNumberTriangular
