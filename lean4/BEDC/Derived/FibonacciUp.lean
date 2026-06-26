import BEDC.Derived.Window6FibonacciCount
import BEDC.Derived.Window6LucasCount
import BEDC.Derived.Window6TransferMatrix
import BEDC.Derived.Window6TraceLucas

namespace BEDC.Derived.FibonacciUp

abbrev fib : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.fib

abbrev lucas : Nat -> Nat :=
  BEDC.Derived.Window6Lucas.lucas

abbrev altSign : Nat -> Int :=
  BEDC.Derived.Window6Transfer.altSign

theorem fib_zero : fib 0 = 0 := by
  rfl

theorem fib_one : fib 1 = 1 := by
  rfl

theorem fib_recurrence (n : Nat) :
    fib (n + 2) = fib (n + 1) + fib n := by
  rfl

theorem lucas_zero : lucas 0 = 2 := by
  rfl

theorem lucas_one : lucas 1 = 1 := by
  rfl

theorem lucas_recurrence (n : Nat) :
    lucas (n + 2) = lucas (n + 1) + lucas n := by
  rfl

theorem lucas_eq_fib_add (n : Nat) :
    lucas (n + 1) = fib (n + 2) + fib n :=
  BEDC.Derived.Window6Lucas.lucas_eq_fib_add n

theorem transfer_power_fib (n : Nat) :
    BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M (n + 1) =
      ⟨((fib (n + 2) : Nat) : Int),
        ((fib (n + 1) : Nat) : Int),
        ((fib (n + 1) : Nat) : Int),
        ((fib n : Nat) : Int)⟩ :=
  BEDC.Derived.Window6Transfer.M_pow_fib n

theorem trace_transfer_power_eq_lucas (n : Nat) :
    BEDC.Derived.Window6Transfer.trace
      (BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M n) =
      ((lucas n : Nat) : Int) :=
  BEDC.Derived.Window6TraceLucas.trace_M_pow_eq_lucas n

theorem cassini_matrix (n : Nat) :
    BEDC.Derived.Window6Transfer.det
      (BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M n) =
      altSign n :=
  BEDC.Derived.Window6Transfer.cassini n

theorem cassini_shifted (n : Nat) :
    (((fib (n + 2) * fib n : Nat) : Int) -
      ((fib (n + 1) * fib (n + 1) : Nat) : Int)) =
      altSign (n + 1) := by
  have h := cassini_matrix (n + 1)
  rw [transfer_power_fib n] at h
  exact h

theorem cassini (n : Nat) :
    (((fib (n + 1 + 1) * fib n : Nat) : Int) -
      ((fib (n + 1) * fib (n + 1) : Nat) : Int)) =
      altSign (n + 1) :=
  cassini_shifted n

theorem cassini_succ_index (n : Nat) :
    (((fib ((n + 1) + 1) * fib n : Nat) : Int) -
      ((fib (n + 1) * fib (n + 1) : Nat) : Int)) =
      altSign (n + 1) :=
  cassini n

end BEDC.Derived.FibonacciUp
