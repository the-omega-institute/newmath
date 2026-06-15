import BEDC.Derived.Window6TransferMatrix
import BEDC.Derived.Window6LucasCount

namespace BEDC.Derived.Window6TraceLucas

abbrev fib : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.fib

abbrev lucas : Nat -> Nat :=
  BEDC.Derived.Window6Lucas.lucas

/--
The trace identity is the algebraic bridge between the transfer matrix
`M = [[1, 1], [1, 0]]` and the Window6 cyclic count: the trace of `M^n`
is the Lucas number `L_n`, matching the Python forward proof of the
cycle no-adjacent-one count `trace(M^m) = L_m`.  This file connects the
checked Fibonacci power formula for `M` with the checked Fibonacci-Lucas
formula, without extra assumptions or placeholder proofs.
-/
theorem trace_M_pow_succ_eq_lucas (n : Nat) :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow
        BEDC.Derived.Window6Transfer.M (n + 1)) =
      ((lucas (n + 1) : Nat) : Int) := by
  rw [BEDC.Derived.Window6Transfer.M_pow_fib n]
  unfold BEDC.Derived.Window6Transfer.trace
  change (((fib (n + 2) : Nat) : Int) + ((fib n : Nat) : Int)) =
    ((BEDC.Derived.Window6Lucas.lucas (n + 1) : Nat) : Int)
  rw [BEDC.Derived.Window6Lucas.lucas_eq_fib_add n]
  rfl

theorem trace_M_pow_eq_lucas (n : Nat) :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow
        BEDC.Derived.Window6Transfer.M n) =
      ((lucas n : Nat) : Int) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      exact trace_M_pow_succ_eq_lucas n

example :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 6) =
      ((lucas 6 : Nat) : Int) := by
  exact trace_M_pow_eq_lucas 6

example :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 1) =
      ((lucas 1 : Nat) : Int) := by
  exact trace_M_pow_eq_lucas 1

theorem trace_M_pow_six_value :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 6) =
      18 := by
  rfl

theorem trace_M_pow_one_value :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 1) =
      1 := by
  rfl

end BEDC.Derived.Window6TraceLucas
