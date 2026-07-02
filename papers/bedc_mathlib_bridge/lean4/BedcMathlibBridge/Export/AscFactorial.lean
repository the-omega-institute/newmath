import BedcMathlibBridge.Constructive.AscFactorial

namespace BedcMathlibBridge.Export.AscFactorial

open BedcMathlibBridge.Constructive.AscFactorial

structure AscFactorialExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ x k : Nat, readback x k = toNat x k
  bedc_apply : ∀ x k : Nat,
    readback x k = BEDC.Derived.StirlingCycleUp.risingFactorialValue x k
  zero_apply : ∀ x : Nat, readback x 0 = 1
  recurrence_apply : ∀ x k : Nat,
    readback x (Nat.succ k) = readback x k * (x + k)
  ascFactorial_apply : ∀ x k : Nat, readback x k = Nat.ascFactorial x k

def ascFactorialExport : AscFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro x k
    rfl
  bedc_apply := by
    intro x k
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  ascFactorial_apply := toNat_eq_ascFactorial

theorem risingFactorialValue_eq_ascFactorial (x k : Nat) :
    BEDC.Derived.StirlingCycleUp.risingFactorialValue x k =
      Nat.ascFactorial x k :=
  BedcMathlibBridge.Constructive.AscFactorial.toNat_eq_ascFactorial x k

end BedcMathlibBridge.Export.AscFactorial
