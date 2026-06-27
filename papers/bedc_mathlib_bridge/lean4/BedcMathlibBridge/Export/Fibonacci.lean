import BedcMathlibBridge.Constructive.Fibonacci

namespace BedcMathlibBridge.Export.Fibonacci

open BedcMathlibBridge.Constructive.Fibonacci

structure FibonacciExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat, readback n = BEDC.Derived.FibonacciUp.fib n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  recurrence_apply : ∀ n : Nat, readback (n + 2) = readback n + readback (n + 1)
  nat_fib_apply : ∀ n : Nat, readback n = Nat.fib n

def fibonacciExport : FibonacciExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  one_apply := toNat_one
  recurrence_apply := toNat_recurrence_mathlib_order
  nat_fib_apply := toNat_eq_nat_fib

theorem fib_eq_nat_fib (n : Nat) :
    BEDC.Derived.FibonacciUp.fib n = Nat.fib n := by
  change toNat n = Nat.fib n
  exact toNat_eq_nat_fib n

end BedcMathlibBridge.Export.Fibonacci
