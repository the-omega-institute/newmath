import BedcMathlibBridge.Constructive.Lah

namespace BedcMathlibBridge.Export.Lah

open BedcMathlibBridge.Constructive.Lah

structure LahFirstColumnExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = firstColumnToNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1
  nat_factorial_apply : ∀ n : Nat, readback n = Nat.factorial (Nat.succ n)
  recurrence_apply : ∀ n : Nat,
    readback (Nat.succ n) = Nat.succ (Nat.succ n) * readback n

def lahFirstColumnExport : LahFirstColumnExportWitness where
  readback := firstColumnToNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := firstColumnToNat_apply
  nat_factorial_apply := firstColumnToNat_eq_nat_factorial_succ
  recurrence_apply := firstColumnToNat_succ_recurrence_mathlib

theorem lahNumber_succ_one_eq_nat_factorial_succ (n : Nat) :
    BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 =
      Nat.factorial (Nat.succ n) := by
  change firstColumnToNat n = Nat.factorial (Nat.succ n)
  exact firstColumnToNat_eq_nat_factorial_succ n

end BedcMathlibBridge.Export.Lah
