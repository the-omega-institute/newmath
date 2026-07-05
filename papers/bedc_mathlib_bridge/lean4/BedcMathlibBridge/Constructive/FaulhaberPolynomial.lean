import BedcMathlibBridge.Export.Triangular
import BEDC.Derived.FaulhaberPolynomialUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Faulhaber low-order closed numerator correspondence.

`BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n` is the
scaled numerator `n * (n + 1)` appearing in the checked low-order Faulhaber
window

  `2 * powerSumNat 1 n = triangularClosedNumerator n`.

The bridge transports the same numerator to mathlib's binomial presentation
`2 * Nat.choose (n + 1) 2`, using BEDC's triangular closed form and the existing
triangular-number bridge.
-/

namespace BedcMathlibBridge.Constructive.FaulhaberPolynomial

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC triangular closed numerator. -/
def triangularClosedNumeratorToNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n

theorem triangularClosedNumeratorToNat_eq_bedc (n : Nat) :
    triangularClosedNumeratorToNat n =
      BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n :=
  rfl

theorem triangularClosedNumeratorToNat_eq_mul_succ (n : Nat) :
    triangularClosedNumeratorToNat n = n * (n + 1) :=
  rfl

theorem triangularClosedNumeratorToNat_zero :
    triangularClosedNumeratorToNat 0 = 0 :=
  rfl

theorem triangularClosedNumeratorToNat_powerSum_scaled (n : Nat) :
    2 * BEDC.Derived.FaulhaberUp.powerSumNat 1 n =
      triangularClosedNumeratorToNat n := by
  change
    2 * BEDC.Derived.FaulhaberUp.powerSumNat 1 n =
      BEDC.Derived.FaulhaberPolynomialUp.triangularClosedNumerator n
  exact BEDC.Derived.FaulhaberPolynomialUp.powerSum_one_triangular_closed_scaled n

theorem triangularClosedNumeratorToNat_eq_two_mul_triangular (n : Nat) :
    triangularClosedNumeratorToNat n =
      2 * BEDC.Derived.PolygonalUp.triangularNumber n := by
  calc
    triangularClosedNumeratorToNat n = n * (n + 1) := rfl
    _ = 2 * BEDC.Derived.PolygonalUp.triangularNumber n := by
      exact (BEDC.Derived.PolygonalUp.triangular_double_eq_mul_succ n).symm

theorem triangularClosedNumeratorToNat_eq_two_mul_nat_choose (n : Nat) :
    triangularClosedNumeratorToNat n = 2 * Nat.choose (n + 1) 2 := by
  rw [triangularClosedNumeratorToNat_eq_two_mul_triangular n]
  have h : BEDC.Derived.PolygonalUp.triangularNumber n = Nat.choose (n + 1) 2 :=
    BedcMathlibBridge.Export.Triangular.triangularNumber_eq_nat_choose n
  exact congrArg (fun t => 2 * t) h

end BedcMathlibBridge.Constructive.FaulhaberPolynomial
