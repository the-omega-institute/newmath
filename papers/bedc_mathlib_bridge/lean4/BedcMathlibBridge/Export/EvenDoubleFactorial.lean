import BedcMathlibBridge.Constructive.EvenDoubleFactorial

namespace BedcMathlibBridge.Export.EvenDoubleFactorial

open BedcMathlibBridge.Constructive.EvenDoubleFactorial

structure EvenDoubleFactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat,
    readback n =
      BEDC.Derived.JacobsthalUp.powTwo n *
        BEDC.Derived.HyperfactorialUp.factorialNat n
  zero_apply : readback 0 = 1
  recurrence_apply : forall n : Nat,
    readback (Nat.succ n) = 2 * Nat.succ n * readback n
  double_factorial_apply : forall n : Nat,
    readback n = Nat.doubleFactorial (2 * n)

def evenDoubleFactorialExport : EvenDoubleFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  double_factorial_apply := toNat_eq_doubleFactorial_even

theorem evenDoubleFactorial_eq_doubleFactorial (n : Nat) :
    BEDC.Derived.JacobsthalUp.powTwo n *
        BEDC.Derived.HyperfactorialUp.factorialNat n =
      Nat.doubleFactorial (2 * n) :=
  BedcMathlibBridge.Constructive.EvenDoubleFactorial.toNat_eq_doubleFactorial_even n

end BedcMathlibBridge.Export.EvenDoubleFactorial
