import BEDC.Derived.SquarePyramidalUp
import BEDC.Derived.PolygonalUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Square pyramidal number structural correspondence.

`BEDC.Derived.SquarePyramidalUp.squarePyramidalNumber n` is the `n`-th square
pyramidal number, defined in BEDC by the prefix-sum recurrence
`P (n+1) = P n + squareNumber (n+1)` (the sum `1^2 + ... + n^2`). Its genuine
mathlib correspondence is the binomial identity

  `squarePyramidalNumber n = Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3`,

which expresses the sum of squares through mathlib's `Nat.choose`. The proof is
a `Nat` induction driven by the BEDC recurrence and Pascal's rule
(`Nat.choose_succ_succ`); the auxiliary binomial facts `choose (n+1) 1 = n + 1`
and `2 * choose (n+1) 2 = (n+1) * n` are re-derived here `0`-axiom rather than
cited from mathlib (mathlib's `Nat.choose_one_right` carries `propext`), keeping
the whole correspondence free of `Classical.choice`, `Quot.sound` and `propext`.
The plain closed form `n * (n+1) * (2*n+1) / 6` is core `Nat` arithmetic, not a
mathlib target.
-/

namespace BedcMathlibBridge.Constructive.SquarePyramidal

open BEDC.Derived.SquarePyramidalUp (squarePyramidalNumber squarePyramidal_succ)
open BEDC.Derived.PolygonalUp (squareNumber)

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

/-- `0`-axiom re-derivation of `2 * Nat.choose (n+1) 2 = (n+1) * n`, division-free
via Pascal's rule (mathlib's `Nat.choose_two_right` states `n * (n-1) / 2`). -/
private theorem two_mul_choose_two (n : Nat) :
    2 * Nat.choose (n + 1) 2 = (n + 1) * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.choose_succ_succ (n + 1) 1, Nat.mul_add, ih, choose_one_right']
      calc 2 * (n + 1) + (n + 1) * n
          = (n + 1) * 2 + (n + 1) * n := by rw [Nat.mul_comm 2 (n + 1)]
        _ = (n + 1) * (2 + n) := (Nat.mul_add (n + 1) 2 n).symm
        _ = (n + 1) * (n + 2) := by rw [Nat.add_comm 2 n]
        _ = (n + 1 + 1) * (n + 1) := by rw [Nat.mul_comm (n + 1) (n + 2)]

/-- The additive rearrangement carrying the induction step. -/
private theorem sp_ac (c2 c3 a b : Nat) :
    (c2 + 2 * c3) + (a + b) = (a + c2) + (b + 2 * c3) := by
  calc (c2 + 2 * c3) + (a + b)
      = c2 + (2 * c3 + (a + b)) := Nat.add_assoc c2 (2 * c3) (a + b)
    _ = c2 + (a + (b + 2 * c3)) := by
          rw [Nat.add_comm (2 * c3) (a + b), Nat.add_assoc a b (2 * c3)]
    _ = (c2 + a) + (b + 2 * c3) := (Nat.add_assoc c2 a (b + 2 * c3)).symm
    _ = (a + c2) + (b + 2 * c3) := by rw [Nat.add_comm c2 a]

/-- Direct `Nat` readback of the BEDC square pyramidal number. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  squarePyramidalNumber n

theorem toNat_eq_squarePyramidalNumber (n : Nat) :
    toNat n = squarePyramidalNumber n :=
  rfl

/-- Boundary: the `0`-th square pyramidal number is `0`. -/
theorem toNat_zero : toNat 0 = 0 := by
  rfl

/-- Boundary: the first square pyramidal number is `1`. -/
theorem toNat_one : toNat 1 = 1 := by
  rfl

/-- The BEDC square pyramidal recurrence `P (n+1) = P n + squareNumber (n+1)`,
transported through the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + squareNumber (Nat.succ n) := by
  change
    squarePyramidalNumber (Nat.succ n) =
      squarePyramidalNumber n + squareNumber (Nat.succ n)
  exact squarePyramidal_succ n

/-- The main structural correspondence: the BEDC square pyramidal number is the
binomial sum `Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3`. -/
theorem toNat_eq_nat_choose_sum (n : Nat) :
    toNat n = Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3 := by
  change squarePyramidalNumber n = _
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [squarePyramidal_succ, ih]
      show (Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3) + squareNumber (n + 1)
        = Nat.choose (n + 2) 2 + 2 * Nat.choose (n + 2) 3
      rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_succ_succ (n + 1) 2,
          choose_one_right', Nat.mul_add]
      have hsq : squareNumber (n + 1) = (n + 1) + (n + 1) * n := by
        show (n + 1) * (n + 1) = (n + 1) + (n + 1) * n
        rw [Nat.mul_succ, Nat.add_comm]
      rw [hsq, two_mul_choose_two n]
      exact sp_ac (Nat.choose (n + 1) 2) (Nat.choose (n + 1) 3) (n + 1) ((n + 1) * n)

end BedcMathlibBridge.Constructive.SquarePyramidal
