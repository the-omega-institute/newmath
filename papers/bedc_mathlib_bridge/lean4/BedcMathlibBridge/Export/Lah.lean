import BedcMathlibBridge.Constructive.Lah

/-!
Export witness for the Lah first-column factorial correspondence.
-/

namespace BedcMathlibBridge.Export.Lah

open BedcMathlibBridge.Constructive.Lah

structure LahFirstColumnExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat,
    readback n = BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1
  zero_apply : readback 0 = 1
  bedc_factorial_apply : forall n : Nat,
    readback n = BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n)
  nat_factorial_apply : forall n : Nat,
    readback n = Nat.factorial (Nat.succ n)

def lahFirstColumnExport : LahFirstColumnExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  bedc_factorial_apply := toNat_eq_stirling_factorial_succ
  nat_factorial_apply := toNat_eq_nat_factorial_succ

theorem lahNumber_succ_one_eq_nat_factorial (n : Nat) :
    BEDC.Derived.LahUp.lahNumber (Nat.succ n) 1 =
      Nat.factorial (Nat.succ n) :=
  BedcMathlibBridge.Constructive.Lah.toNat_eq_nat_factorial_succ n

end BedcMathlibBridge.Export.Lah
