import BedcMathlibBridge.Constructive.Superfactorial

namespace BedcMathlibBridge.Export.Superfactorial

open BedcMathlibBridge.Constructive.Superfactorial

structure SuperfactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat, readback n = BEDC.Derived.HyperfactorialUp.superfactorial n
  zero_apply : readback 0 = 1
  recurrence_apply : ∀ n : Nat,
    readback (Nat.succ n) =
      readback n * BEDC.Derived.HyperfactorialUp.factorialNat (Nat.succ n)
  superFactorial_apply : ∀ n : Nat, readback n = Nat.superFactorial n

def superfactorialExport : SuperfactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  superFactorial_apply := toNat_eq_superFactorial

theorem superfactorial_eq_superFactorial (n : Nat) :
    BEDC.Derived.HyperfactorialUp.superfactorial n = Nat.superFactorial n :=
  BedcMathlibBridge.Constructive.Superfactorial.toNat_eq_superFactorial n

end BedcMathlibBridge.Export.Superfactorial
