import BEDC.Derived.PolygonalUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Pentagonal number structural correspondence.

`BEDC.Derived.PolygonalUp.pentagonalNumber n` is the `n`-th pentagonal number,
defined in BEDC by the recurrence `P (n+1) = P n + (3*n + 1)`. Its genuine
mathlib correspondence is the binomial identity

  `pentagonalNumber n = 3 * Nat.choose n 2 + n`,

expressing `n * (3*n - 1) / 2` through mathlib's `Nat.choose`. The proof is a
`Nat` induction driven by the BEDC recurrence and Pascal's rule
(`Nat.choose_succ_succ`); the auxiliary fact `choose n 1 = n` is re-derived here
`0`-axiom (mathlib's `Nat.choose_one_right` carries `propext`), keeping the whole
correspondence free of `Classical.choice`, `Quot.sound` and `propext`.
-/

namespace BedcMathlibBridge.Constructive.Pentagonal

open BEDC.Derived.PolygonalUp (pentagonalNumber pentagonal_succ)

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

/-- Direct `Nat` readback of the BEDC pentagonal number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  pentagonalNumber n

theorem toNat_eq_pentagonalNumber (n : Nat) :
    toNat n = pentagonalNumber n :=
  rfl

/-- Boundary: the `0`-th pentagonal number is `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first pentagonal number is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The BEDC pentagonal recurrence `P (n+1) = P n + (3*n + 1)`, transported
through the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + (3 * n + 1) := by
  change pentagonalNumber (Nat.succ n) = pentagonalNumber n + (3 * n + 1)
  exact pentagonal_succ n

/-- The main structural correspondence: the BEDC pentagonal number is the
binomial expression `3 * Nat.choose n 2 + n`. -/
theorem toNat_eq_nat_choose (n : Nat) :
    toNat n = 3 * Nat.choose n 2 + n := by
  change pentagonalNumber n = _
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pentagonal_succ, ih]
      rw [Nat.choose_succ_succ n 1, choose_one_right', Nat.mul_add]
      calc (3 * Nat.choose n 2 + n) + (3 * n + 1)
          = 3 * Nat.choose n 2 + (n + (3 * n + 1)) :=
            Nat.add_assoc _ n (3 * n + 1)
        _ = 3 * Nat.choose n 2 + ((3 * n) + (n + 1)) := by
              rw [Nat.add_comm n (3 * n + 1), Nat.add_assoc (3 * n) 1 n,
                  Nat.add_comm 1 n]
        _ = (3 * Nat.choose n 2 + 3 * n) + (n + 1) :=
              (Nat.add_assoc (3 * Nat.choose n 2) (3 * n) (n + 1)).symm
        _ = (3 * n + 3 * Nat.choose n 2) + (n + 1) := by
              rw [Nat.add_comm (3 * Nat.choose n 2) (3 * n)]

end BedcMathlibBridge.Constructive.Pentagonal
