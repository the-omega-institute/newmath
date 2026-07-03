import BedcMathlibBridge.Constructive.Leonardo

/-!
Export witness for the BEDC Leonardo-number readback.
-/

namespace BedcMathlibBridge.Export.Leonardo

open BedcMathlibBridge.Constructive.Leonardo

structure LeonardoExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.LeonardoNumberUp.leonardoNumber n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 1
  recurrence_apply : forall n : Nat,
    readback (n + 2) = readback (n + 1) + readback n + 1
  nat_fib_formula_apply : forall n : Nat,
    readback n = 2 * Nat.fib (n + 1) - 1

def leonardoExport : LeonardoExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  one_apply := toNat_one
  recurrence_apply := toNat_recurrence
  nat_fib_formula_apply := toNat_eq_nat_fib_formula

theorem leonardoNumber_eq_nat_fib_formula (n : Nat) :
    BEDC.Derived.LeonardoNumberUp.leonardoNumber n =
      2 * Nat.fib (n + 1) - 1 := by
  change toNat n = 2 * Nat.fib (n + 1) - 1
  exact BedcMathlibBridge.Constructive.Leonardo.toNat_eq_nat_fib_formula n

end BedcMathlibBridge.Export.Leonardo
