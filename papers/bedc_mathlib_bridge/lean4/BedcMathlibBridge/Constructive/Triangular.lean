import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.TetrahedralUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Triangular number structural correspondence.

`BEDC.Derived.PolygonalUp.triangularNumber n` is the `n`-th triangular number.
BEDC verifies the binomial-row identity
`triangularNumber n = C (n + 1) 2` (`BEDC.Derived.TetrahedralUp.T_eq_binomial`),
where `C = BEDC.Derived.BinomialIdentitiesUp.C` is the closed-generation Pascal
count, definitionally equal to `BEDC.Derived.LucasTheoremUp.bedcChooseNat`. The
already-verified bridge lemma `Constructive.Binomial.bedcChoose_eq_nat_choose`
transports the readback to mathlib's `Nat.choose`, giving

  `triangularNumber n = Nat.choose (n + 1) 2`.
-/

namespace BedcMathlibBridge.Constructive.Triangular

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC triangular number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.PolygonalUp.triangularNumber n

theorem toNat_eq_triangularNumber (n : Nat) :
    toNat n = BEDC.Derived.PolygonalUp.triangularNumber n :=
  rfl

/-- Boundary: the `0`-th triangular number is `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first triangular number is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The BEDC triangular recurrence `T (n+1) = T n + (n+1)`, transported through
the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + Nat.succ n := by
  change
    BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n) =
      BEDC.Derived.PolygonalUp.triangularNumber n + Nat.succ n
  exact BEDC.Derived.PolygonalUp.triangular_succ n

/-- The main structural correspondence: the BEDC triangular number equals
mathlib's `Nat.choose (n + 1) 2`. -/
theorem toNat_eq_nat_choose (n : Nat) :
    toNat n = Nat.choose (n + 1) 2 := by
  have hBedc :
      BEDC.Derived.PolygonalUp.triangularNumber n =
        BEDC.Derived.LucasTheoremUp.bedcChooseNat (n + 1) 2 := by
    have hC := BEDC.Derived.TetrahedralUp.T_eq_binomial n
    change
      BEDC.Derived.PolygonalUp.triangularNumber n =
        BEDC.Derived.BinomialIdentitiesUp.C (n + 1) 2 at hC
    rw [hC]
    rfl
  calc
    toNat n = BEDC.Derived.PolygonalUp.triangularNumber n := rfl
    _ = BEDC.Derived.LucasTheoremUp.bedcChooseNat (n + 1) 2 := hBedc
    _ = Nat.choose (n + 1) 2 :=
      BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose (n + 1) 2

end BedcMathlibBridge.Constructive.Triangular
