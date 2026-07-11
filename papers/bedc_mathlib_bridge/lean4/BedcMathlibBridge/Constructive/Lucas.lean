import BedcMathlibBridge.Constructive.Fibonacci

/-!
Lucas count readback.

`BEDC.Derived.FibonacciUp.lucas` is the Window6 cyclic no-adjacent-one count.
mathlib has `Nat.fib` but no separate `Nat.lucas`; the thin exported surface
therefore anchors the BEDC Lucas count to the standard Fibonacci expression
`Nat.fib (n + 2) + Nat.fib n`.
-/

namespace BedcMathlibBridge.Constructive.Lucas

private def mathlibFibProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.fib n = Nat.fib n := fun _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC Lucas count. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibFibProvenanceAnchor
  BEDC.Derived.FibonacciUp.lucas n

theorem toNat_eq_bedc_lucas (n : Nat) :
    toNat n = BEDC.Derived.FibonacciUp.lucas n :=
  rfl

theorem toNat_zero : toNat 0 = 2 := by
  rfl

theorem toNat_one : toNat 1 = 1 := by
  rfl

theorem toNat_recurrence (n : Nat) :
    toNat (n + 2) = toNat (n + 1) + toNat n := by
  rfl

theorem bedc_fib_eq_nat_fib (n : Nat) :
    BEDC.Derived.FibonacciUp.fib n = Nat.fib n := by
  change BedcMathlibBridge.Constructive.Fibonacci.toNat n = Nat.fib n
  exact BedcMathlibBridge.Constructive.Fibonacci.toNat_eq_nat_fib n

/-- The BEDC Lucas count at `n + 1` is the standard Fibonacci expression. -/
theorem toNat_succ_eq_nat_fib_add (n : Nat) :
    toNat (n + 1) = Nat.fib (n + 2) + Nat.fib n := by
  calc
    toNat (n + 1) =
        BEDC.Derived.FibonacciUp.fib (n + 2) +
          BEDC.Derived.FibonacciUp.fib n :=
      BEDC.Derived.FibonacciUp.lucas_eq_fib_add n
    _ = Nat.fib (n + 2) + Nat.fib n := by
      rw [bedc_fib_eq_nat_fib (n + 2), bedc_fib_eq_nat_fib n]

end BedcMathlibBridge.Constructive.Lucas
