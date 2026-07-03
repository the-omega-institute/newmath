import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.TetrahedralUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Tetrahedral number structural correspondence.

`BEDC.Derived.TetrahedralUp.tetrahedralNumber n` is the `n`-th tetrahedral
number, defined in BEDC as the binomial value `C (n + 2) 3` where
`C = BEDC.Derived.BinomialIdentitiesUp.C` is the closed-generation Pascal count.
Since that count is definitionally `BEDC.Derived.LucasTheoremUp.bedcChooseNat`
(both unfold to `bwordLength (natChooseFn (natToUnary n) (natToUnary k))`), the
already-verified bridge lemma `Constructive.Binomial.bedcChoose_eq_nat_choose`
transports the readback to mathlib's `Nat.choose`, giving the pointwise equality

  `tetrahedralNumber n = Nat.choose (n + 2) 3`.

The `change` steps align `C` with `bedcChooseNat` by definitional equality,
exactly as in the q-binomial bridge.
-/

namespace BedcMathlibBridge.Constructive.Tetrahedral

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC tetrahedral number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.TetrahedralUp.tetrahedralNumber n

theorem toNat_eq_tetrahedralNumber (n : Nat) :
    toNat n = BEDC.Derived.TetrahedralUp.tetrahedralNumber n :=
  rfl

/-- Boundary: the empty tetrahedron has volume `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first tetrahedral number is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The BEDC tetrahedral recurrence `Te (n+1) = Te n + T (n+1)`, transported
through the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) =
      toNat n + BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n) := by
  change
    BEDC.Derived.TetrahedralUp.tetrahedralNumber (Nat.succ n) =
      BEDC.Derived.TetrahedralUp.tetrahedralNumber n +
        BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n)
  exact BEDC.Derived.TetrahedralUp.tetrahedral_succ n

/-- The main structural correspondence: the BEDC tetrahedral number equals
mathlib's `Nat.choose (n + 2) 3`. -/
theorem toNat_eq_nat_choose (n : Nat) :
    toNat n = Nat.choose (n + 2) 3 := by
  have hBedc :
      BEDC.Derived.TetrahedralUp.tetrahedralNumber n =
        BEDC.Derived.LucasTheoremUp.bedcChooseNat (n + 2) 3 := by
    change
      BEDC.Derived.BinomialIdentitiesUp.C (n + 2) 3 =
        BEDC.Derived.LucasTheoremUp.bedcChooseNat (n + 2) 3
    rfl
  calc
    toNat n = BEDC.Derived.TetrahedralUp.tetrahedralNumber n := rfl
    _ = BEDC.Derived.LucasTheoremUp.bedcChooseNat (n + 2) 3 := hBedc
    _ = Nat.choose (n + 2) 3 :=
      BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose (n + 2) 3

end BedcMathlibBridge.Constructive.Tetrahedral
