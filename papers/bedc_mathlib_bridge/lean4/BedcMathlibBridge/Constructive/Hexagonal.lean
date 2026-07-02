import BEDC.Derived.PolygonalUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Hexagonal number structural correspondence.

The `n`-th hexagonal number is BEDC's general polygonal number
`BEDC.Derived.PolygonalUp.polygonalNumber 6 n`, defined by the recurrence
`P (n+1) = P n + ((6 - 2) * n + 1)`. Its genuine mathlib correspondence is the
binomial identity

  `polygonalNumber 6 n = 4 * Nat.choose n 2 + n`,

expressing `n * (2*n - 1)` through mathlib's `Nat.choose`. The proof is a `Nat`
induction driven by the BEDC recurrence and Pascal's rule
(`Nat.choose_succ_succ`); the auxiliary fact `choose n 1 = n` is re-derived here
`0`-axiom (mathlib's `Nat.choose_one_right` carries `propext`), keeping the whole
correspondence free of `Classical.choice`, `Quot.sound` and `propext`.
-/

namespace BedcMathlibBridge.Constructive.Hexagonal

open BEDC.Derived.PolygonalUp (polygonalNumber polygonal_succ)

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- `0`-axiom re-derivation of `Nat.choose n 1 = n` (mathlib's own
`Nat.choose_one_right` depends on `propext`). -/
private theorem choose_one_right' (n : Nat) : Nat.choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.choose_succ_succ n 0, Nat.choose_zero_right, ih, Nat.add_comm]

/-- Direct `Nat` readback of the BEDC hexagonal number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  polygonalNumber 6 n

theorem toNat_eq_polygonalNumber (n : Nat) :
    toNat n = polygonalNumber 6 n :=
  rfl

/-- Boundary: the `0`-th hexagonal number is `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first hexagonal number is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The BEDC hexagonal recurrence `P (n+1) = P n + (4*n + 1)`, transported through
the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + (4 * n + 1) := by
  change polygonalNumber 6 (Nat.succ n) = polygonalNumber 6 n + (4 * n + 1)
  exact polygonal_succ 6 n

/-- The main structural correspondence: the BEDC hexagonal number is the binomial
expression `4 * Nat.choose n 2 + n`. -/
theorem toNat_eq_nat_choose (n : Nat) :
    toNat n = 4 * Nat.choose n 2 + n := by
  change polygonalNumber 6 n = _
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [polygonal_succ, ih]
      show (4 * Nat.choose n 2 + n) + (4 * n + 1)
        = 4 * Nat.choose (n + 1) 2 + (n + 1)
      rw [Nat.choose_succ_succ n 1, choose_one_right', Nat.mul_add]
      calc (4 * Nat.choose n 2 + n) + (4 * n + 1)
          = 4 * Nat.choose n 2 + (n + (4 * n + 1)) :=
            Nat.add_assoc _ n (4 * n + 1)
        _ = 4 * Nat.choose n 2 + ((4 * n) + (n + 1)) := by
              rw [Nat.add_comm n (4 * n + 1), Nat.add_assoc (4 * n) 1 n,
                  Nat.add_comm 1 n]
        _ = (4 * Nat.choose n 2 + 4 * n) + (n + 1) :=
              (Nat.add_assoc (4 * Nat.choose n 2) (4 * n) (n + 1)).symm
        _ = (4 * n + 4 * Nat.choose n 2) + (n + 1) := by
              rw [Nat.add_comm (4 * Nat.choose n 2) (4 * n)]

end BedcMathlibBridge.Constructive.Hexagonal
