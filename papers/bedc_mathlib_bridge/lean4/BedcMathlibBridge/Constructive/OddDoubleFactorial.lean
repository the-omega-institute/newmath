import BEDC.Derived.EulerianSecondOrderUp
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
Odd double factorial structural correspondence.

`BEDC.Derived.EulerianSecondOrderUp.oddDoubleFactorialCount n` is the product
`1 · 3 · 5 · ⋯ · (2n-1)` of the first `n` odd numbers, defined by the recurrence
`oddDoubleFactorialCount (n+1) = (2n+1) · oddDoubleFactorialCount n` with
`oddDoubleFactorialCount 0 = 1`. This is exactly the odd double factorial
`(2n-1)‼`, so the shifted readback satisfies

  `oddDoubleFactorialCount (n + 1) = Nat.doubleFactorial (2 * n + 1)`,

bridging the BEDC odd double factorial to mathlib's `Nat.doubleFactorial`. The
proof is a direct induction using mathlib's `doubleFactorial_add_two`.
-/

namespace BedcMathlibBridge.Constructive.OddDoubleFactorial

private def mathlibDoubleFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.doubleFactorial n = Nat.doubleFactorial n := fun _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC odd double factorial. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibDoubleFactorialProvenanceAnchor
  BEDC.Derived.EulerianSecondOrderUp.oddDoubleFactorialCount n

theorem toNat_eq_oddDoubleFactorialCount (n : Nat) :
    toNat n = BEDC.Derived.EulerianSecondOrderUp.oddDoubleFactorialCount n :=
  rfl

/-- Boundary: the empty product is `1`. -/
theorem toNat_zero : toNat 0 = 1 := by
  rfl

/-- The BEDC odd double factorial recurrence
`ODF (n+1) = (2n+1) · ODF n`, transported through the readback. -/
theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = Nat.succ (n + n) * toNat n := by
  rfl

/-- The main structural correspondence: the BEDC odd double factorial at `n + 1`
equals mathlib's odd double factorial `Nat.doubleFactorial (2 * n + 1)`. -/
theorem toNat_succ_eq_doubleFactorial (n : Nat) :
    toNat (Nat.succ n) = Nat.doubleFactorial (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hcoeffBedc : Nat.succ (Nat.succ n + Nat.succ n) = 2 * n + 3 := by
        rw [Nat.two_mul, Nat.succ_add, Nat.add_succ]
      have hbedc :
          toNat (Nat.succ (Nat.succ n)) =
            (2 * n + 3) * toNat (Nat.succ n) := by
        rw [toNat_succ (Nat.succ n), hcoeffBedc]
      have hidx : 2 * Nat.succ n + 1 = (2 * n + 1) + 2 := by
        rw [Nat.mul_succ]
      have hcoeff : 2 * n + 3 = (2 * n + 1) + 2 := rfl
      rw [hbedc, ih, hidx, Nat.doubleFactorial_add_two, hcoeff]

end BedcMathlibBridge.Constructive.OddDoubleFactorial
