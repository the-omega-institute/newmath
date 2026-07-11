import BedcMathlibBridge.Constructive.StirlingCycleColumn

namespace BedcMathlibBridge.Export.StirlingCycleColumn

open BedcMathlibBridge.Constructive.StirlingCycleColumn

structure StirlingCycleColumnExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat,
    readback n = BEDC.Derived.StirlingCycleUp.stirlingCycle (Nat.succ n) 1
  zero_apply : readback 0 = 1
  recurrence_apply : forall n : Nat,
    readback (Nat.succ n) = Nat.succ n * readback n
  nat_factorial_apply : forall n : Nat, readback n = Nat.factorial n

def stirlingCycleColumnExport : StirlingCycleColumnExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  nat_factorial_apply := toNat_eq_nat_factorial

theorem stirlingCycle_succ_one_eq_nat_factorial (n : Nat) :
    BEDC.Derived.StirlingCycleUp.stirlingCycle (Nat.succ n) 1 =
      Nat.factorial n :=
  BedcMathlibBridge.Constructive.StirlingCycleColumn.toNat_eq_nat_factorial n

end BedcMathlibBridge.Export.StirlingCycleColumn
