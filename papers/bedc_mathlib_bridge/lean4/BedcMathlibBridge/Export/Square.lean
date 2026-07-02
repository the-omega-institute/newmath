import BedcMathlibBridge.Constructive.Square

/-!
Export witness for the square number structural correspondence.

The witness records that the readback is the BEDC square number
`BEDC.Derived.PolygonalUp.squareNumber`, satisfies both boundaries and the BEDC
square recurrence `S (n+1) = S n + n + (n+1)`, identifies with the fourth
polygonal number, and is pointwise equal to mathlib's
`Nat.choose (n + 1) 2 + Nat.choose n 2` (the sum of two consecutive triangular
numbers). The core-`Nat` closed form `n * n` is recorded as a secondary field.
-/

namespace BedcMathlibBridge.Export.Square

open BedcMathlibBridge.Constructive.Square

structure SquareExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PolygonalUp.squareNumber n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  succ_apply : ∀ n : Nat, readback (Nat.succ n) = readback n + n + Nat.succ n
  mul_self_apply : ∀ n : Nat, readback n = n * n
  polygonal_four_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PolygonalUp.polygonalNumber 4 n
  nat_choose_apply : ∀ n : Nat,
    readback n = Nat.choose (n + 1) 2 + Nat.choose n 2

def squareExport : SquareExportWitness where
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
  mul_self_apply := toNat_eq_mul_self
  polygonal_four_apply := toNat_eq_polygonal_four
  nat_choose_apply := toNat_eq_nat_choose_sum

theorem squareNumber_eq_nat_choose_sum (n : Nat) :
    BEDC.Derived.PolygonalUp.squareNumber n
      = Nat.choose (n + 1) 2 + Nat.choose n 2 :=
  BedcMathlibBridge.Constructive.Square.toNat_eq_nat_choose_sum n

end BedcMathlibBridge.Export.Square
