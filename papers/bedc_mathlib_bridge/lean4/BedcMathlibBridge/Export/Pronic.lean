import BedcMathlibBridge.Constructive.Pronic

/-!
Export witness for the pronic (oblong) number structural correspondence.

The witness records that the readback is the BEDC pronic number
`BEDC.Derived.PronicNumberUp.pronicNumber`, has closed form `n * (n + 1)`,
satisfies both boundaries, equals twice the BEDC triangular number, is pointwise
equal to mathlib's `2 * Nat.choose (n + 1) 2`, and is never a perfect square in
the positive range.
-/

namespace BedcMathlibBridge.Export.Pronic

open BedcMathlibBridge.Constructive.Pronic

structure PronicExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.PronicNumberUp.pronicNumber n
  mul_succ_apply : ∀ n : Nat, readback n = n * (n + 1)
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 2
  two_mul_triangular_apply : ∀ n : Nat,
    readback n = 2 * BEDC.Derived.PolygonalUp.triangularNumber n
  nat_choose_apply : ∀ n : Nat, readback n = 2 * Nat.choose (n + 1) 2
  not_square_apply : ∀ n : Nat,
    0 < n -> BEDC.Derived.PronicNumberUp.IsPerfectSquare (readback n) -> False

def pronicExport : PronicExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  mul_succ_apply := toNat_eq_mul_succ
  zero_apply := toNat_zero
  one_apply := toNat_one
  two_mul_triangular_apply := toNat_eq_two_mul_triangular
  nat_choose_apply := toNat_eq_two_mul_nat_choose
  not_square_apply := pronic_not_perfect_square_of_pos

theorem pronicNumber_eq_two_mul_nat_choose (n : Nat) :
    BEDC.Derived.PronicNumberUp.pronicNumber n = 2 * Nat.choose (n + 1) 2 :=
  BedcMathlibBridge.Constructive.Pronic.toNat_eq_two_mul_nat_choose n

end BedcMathlibBridge.Export.Pronic
