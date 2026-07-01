import BedcMathlibBridge.Constructive.Factorial

namespace BedcMathlibBridge.Export.Factorial

open BEDC.FKernel.ExternalBinary (bwordLength)
open BedcMathlibBridge.Constructive.Factorial

structure FactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n =
      bwordLength
        (BEDC.Derived.FactorialUp.natFactorialFn
          (BEDC.Derived.IntUp.natToUnary n))
  zero_apply : readback 0 = 1
  recurrence_apply : ∀ n : Nat, readback (Nat.succ n) = Nat.succ n * readback n
  nat_factorial_apply : ∀ n : Nat, readback n = Nat.factorial n
  relation_apply : ∀ (n : Nat) (f : BEDC.FKernel.Hist.BHist),
    BEDC.Derived.FactorialUp.NatFactorial (BEDC.Derived.IntUp.natToUnary n) f ->
      bwordLength f = Nat.factorial n

def factorialExport : FactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ_mul
  nat_factorial_apply := toNat_eq_nat_factorial
  relation_apply := natFactorial_relation_eq_nat_factorial

theorem natFactorial_eq_nat_factorial
    (n : Nat) (f : BEDC.FKernel.Hist.BHist)
    (factorial :
      BEDC.Derived.FactorialUp.NatFactorial
        (BEDC.Derived.IntUp.natToUnary n) f) :
    bwordLength f = Nat.factorial n :=
  BedcMathlibBridge.Constructive.Factorial.natFactorial_relation_eq_nat_factorial
    n f factorial

end BedcMathlibBridge.Export.Factorial
