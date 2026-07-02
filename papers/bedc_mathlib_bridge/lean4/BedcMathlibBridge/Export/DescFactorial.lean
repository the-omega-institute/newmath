import BedcMathlibBridge.Constructive.DescFactorial

namespace BedcMathlibBridge.Export.DescFactorial

open BedcMathlibBridge.Constructive.DescFactorial

structure DescFactorialExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ x k : Nat, readback x k = toNat x k
  bedc_apply : ∀ x k : Nat,
    readback x k = BEDC.Derived.StirlingSecondCompleteUp.fallingFactorial x k
  zero_apply : ∀ x : Nat, readback x 0 = 1
  recurrence_apply : ∀ x k : Nat,
    readback x (Nat.succ k) = readback x k * (x - k)
  descFactorial_apply : ∀ x k : Nat, readback x k = Nat.descFactorial x k

def descFactorialExport : DescFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro x k
    rfl
  bedc_apply := by
    intro x k
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  descFactorial_apply := toNat_eq_descFactorial

theorem fallingFactorial_eq_descFactorial (x k : Nat) :
    BEDC.Derived.StirlingSecondCompleteUp.fallingFactorial x k =
      Nat.descFactorial x k :=
  BedcMathlibBridge.Constructive.DescFactorial.toNat_eq_descFactorial x k

end BedcMathlibBridge.Export.DescFactorial
