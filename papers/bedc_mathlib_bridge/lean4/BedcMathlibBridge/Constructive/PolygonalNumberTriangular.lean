import BEDC.Derived.PolygonalNumberUp
import Mathlib.Data.Nat.Choose.Basic

/-!
PolygonalNumberUp triangular number structural correspondence.

`BEDC.Derived.PolygonalNumberUp.triangularNumber n` is the BEDC triangular
number surface exposed by `PolygonalNumberUp`. The bridge target is the
mathlib binomial expression

  `Nat.choose (n + 1) 2`.

The proof is a pointwise Pascal induction using the BEDC triangular recurrence
and mathlib's `Nat.choose_succ_succ`; the auxiliary fact `choose n 1 = n` is
re-derived here without importing mathlib's proposition-extensionality-backed
lemma.
-/

namespace BedcMathlibBridge.Constructive.PolygonalNumberTriangular

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

private theorem choose_one_right' (n : Nat) : Nat.choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.choose_succ_succ n 0, Nat.choose_zero_right, ih, Nat.add_comm]

/-- Direct `Nat` readback of the `PolygonalNumberUp` BEDC triangular number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.PolygonalNumberUp.triangularNumber n

theorem toNat_eq_triangularNumber (n : Nat) :
    toNat n = BEDC.Derived.PolygonalNumberUp.triangularNumber n :=
  rfl

theorem toNat_zero : toNat 0 = 0 := by
  rfl

theorem toNat_one : toNat 1 = 1 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + Nat.succ n := by
  change
    BEDC.Derived.PolygonalNumberUp.triangularNumber (Nat.succ n) =
      BEDC.Derived.PolygonalNumberUp.triangularNumber n + Nat.succ n
  exact BEDC.Derived.PolygonalUp.triangular_succ n

theorem toNat_eq_nat_choose (n : Nat) :
    toNat n = Nat.choose (n + 1) 2 := by
  change BEDC.Derived.PolygonalNumberUp.triangularNumber n = Nat.choose (n + 1) 2
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        BEDC.Derived.PolygonalNumberUp.triangularNumber (Nat.succ n)
            = BEDC.Derived.PolygonalNumberUp.triangularNumber n + Nat.succ n :=
              BEDC.Derived.PolygonalUp.triangular_succ n
        _ = Nat.choose (n + 1) 2 + Nat.succ n := by
              rw [ih]
        _ = Nat.succ n + Nat.choose (n + 1) 2 := Nat.add_comm _ _
        _ = Nat.choose (Nat.succ n + 1) 2 := by
              rw [Nat.choose_succ_succ (n + 1) 1, choose_one_right']

end BedcMathlibBridge.Constructive.PolygonalNumberTriangular
