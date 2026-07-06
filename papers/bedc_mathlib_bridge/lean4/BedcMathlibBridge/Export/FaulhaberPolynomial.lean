import BedcMathlibBridge.Constructive.FaulhaberPolynomial

/-!
Export witness for the Faulhaber triangular closed numerator correspondence.

The witness records that the readback is the BEDC low-order Faulhaber numerator
`BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator`, consumes the
checked scaled power-sum theorem, and is pointwise equal to mathlib's
`2 * Nat.choose (n + 1) 2`.
-/

namespace BedcMathlibBridge.Export.FaulhaberPolynomial

open BedcMathlibBridge.Constructive.FaulhaberPolynomial

structure FaulhaberTriangularClosedNumeratorExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = triangularClosedNumeratorToNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n
  mul_succ_apply : ∀ n : Nat, readback n = n * (n + 1)
  zero_apply : readback 0 = 0
  powerSum_scaled_apply : ∀ n : Nat,
    2 * BEDC.Derived.FaulhaberUp.powerSumNat 1 n = readback n
  two_mul_triangular_apply : ∀ n : Nat,
    readback n = 2 * BEDC.Derived.PolygonalUp.triangularNumber n
  nat_choose_apply : ∀ n : Nat, readback n = 2 * Nat.choose (n + 1) 2

def faulhaberTriangularClosedNumeratorExport :
    FaulhaberTriangularClosedNumeratorExportWitness where
  readback := triangularClosedNumeratorToNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  mul_succ_apply := triangularClosedNumeratorToNat_eq_mul_succ
  zero_apply := triangularClosedNumeratorToNat_zero
  powerSum_scaled_apply := triangularClosedNumeratorToNat_powerSum_scaled
  two_mul_triangular_apply := triangularClosedNumeratorToNat_eq_two_mul_triangular
  nat_choose_apply := triangularClosedNumeratorToNat_eq_two_mul_nat_choose

theorem triangularClosedNumerator_eq_two_mul_nat_choose (n : Nat) :
    BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n =
      2 * Nat.choose (n + 1) 2 :=
  calc
    BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n =
        2 * BEDC.Derived.FaulhaberUp.powerSumNat 1 n := by
      exact (BEDC.Derived.FaulhaberPolynomialUp.powerSum_one_triangular_closed_scaled n).symm
    _ = triangularClosedNumeratorToNat n := by
      exact triangularClosedNumeratorToNat_powerSum_scaled n
    _ = 2 * Nat.choose (n + 1) 2 := by
      exact triangularClosedNumeratorToNat_eq_two_mul_nat_choose n

end BedcMathlibBridge.Export.FaulhaberPolynomial
