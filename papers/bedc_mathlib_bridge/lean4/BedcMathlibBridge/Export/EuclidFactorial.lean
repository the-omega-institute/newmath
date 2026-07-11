import BedcMathlibBridge.Constructive.EuclidFactorial

namespace BedcMathlibBridge.Export.EuclidFactorial

open BedcMathlibBridge.Constructive.EuclidFactorial

structure EuclidFactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat,
    readback n = BEDC.Derived.EuclidFactorialNumberUp.euclidFactorialNumber n
  zero_apply : readback 0 = 2
  recurrence_apply : forall n : Nat,
    readback (Nat.succ n) =
      Nat.succ n * BEDC.Derived.EuclidFactorialNumberUp.factorialNat n + 1
  nat_factorial_apply : forall n : Nat, readback n = Nat.factorial n + 1

def euclidFactorialExport : EuclidFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  nat_factorial_apply := toNat_eq_nat_factorial_add_one

theorem euclidFactorialNumber_eq_nat_factorial_add_one (n : Nat) :
    BEDC.Derived.EuclidFactorialNumberUp.euclidFactorialNumber n =
      Nat.factorial n + 1 :=
  BedcMathlibBridge.Constructive.EuclidFactorial.toNat_eq_nat_factorial_add_one n

end BedcMathlibBridge.Export.EuclidFactorial
