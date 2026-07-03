import BedcMathlibBridge.Constructive.Lucas

/-!
Export witness for the BEDC Lucas count readback.

The witness records the direct BEDC readback, the two boundary values, the
Lucas recurrence, and the shifted pointwise correspondence with mathlib's
`Nat.fib` expression.
-/

namespace BedcMathlibBridge.Export.Lucas

open BedcMathlibBridge.Constructive.Lucas

structure LucasExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat, readback n = BEDC.Derived.FibonacciUp.lucas n
  zero_apply : readback 0 = 2
  one_apply : readback 1 = 1
  recurrence_apply : ∀ n : Nat,
    readback (n + 2) = readback (n + 1) + readback n
  nat_fib_shift_apply : ∀ n : Nat,
    readback (n + 1) = Nat.fib (n + 2) + Nat.fib n

def lucasExport : LucasExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  one_apply := toNat_one
  recurrence_apply := toNat_recurrence
  nat_fib_shift_apply := toNat_succ_eq_nat_fib_add

theorem lucas_succ_eq_nat_fib_add (n : Nat) :
    BEDC.Derived.FibonacciUp.lucas (n + 1) =
      Nat.fib (n + 2) + Nat.fib n := by
  change toNat (n + 1) = Nat.fib (n + 2) + Nat.fib n
  exact BedcMathlibBridge.Constructive.Lucas.toNat_succ_eq_nat_fib_add n

end BedcMathlibBridge.Export.Lucas
