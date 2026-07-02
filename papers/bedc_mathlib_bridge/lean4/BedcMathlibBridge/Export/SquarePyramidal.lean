import BedcMathlibBridge.Constructive.SquarePyramidal

/-!
Export witness for the square pyramidal number structural correspondence.

The witness records that the readback is the BEDC square pyramidal number
`BEDC.Derived.SquarePyramidalUp.squarePyramidalNumber`, satisfies both
boundaries and the BEDC prefix-sum recurrence
`P (n+1) = P n + squareNumber (n+1)`, and is pointwise equal to mathlib's
`Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3`.
-/

namespace BedcMathlibBridge.Export.SquarePyramidal

open BedcMathlibBridge.Constructive.SquarePyramidal

structure SquarePyramidalExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.SquarePyramidalUp.squarePyramidalNumber n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat,
    readback (Nat.succ n) =
      readback n + BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n)
  nat_choose_apply : ∀ n : Nat,
    readback n = Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3

def squarePyramidalExport : SquarePyramidalExportWitness where
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
  nat_choose_apply := toNat_eq_nat_choose_sum

theorem squarePyramidalNumber_eq_nat_choose_sum (n : Nat) :
    BEDC.Derived.SquarePyramidalUp.squarePyramidalNumber n
      = Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3 :=
  BedcMathlibBridge.Constructive.SquarePyramidal.toNat_eq_nat_choose_sum n

end BedcMathlibBridge.Export.SquarePyramidal
