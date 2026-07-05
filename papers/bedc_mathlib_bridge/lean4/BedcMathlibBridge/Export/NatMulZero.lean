import BedcMathlibBridge.Constructive.NatMulZero

namespace BedcMathlibBridge.Export.NatMulZero

open BedcMathlibBridge.Constructive.NatMulZero

structure NatMulZeroExportWitness where
  readback : ∀ n : Nat, n * 0 = 0
  readback_apply : ∀ n : Nat, readback n = mulZeroReadback n
  mathlib_apply : ∀ n : Nat, readback n = Nat.mul_zero n
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natMulZeroExport : NatMulZeroExportWitness where
  readback := mulZeroReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := mulZeroReadback_eq_nat_mul_zero
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_mul_zero_mathlib_correspondence (n : Nat) :
    mulZeroReadback n = Nat.mul_zero n := by
  exact mulZeroReadback_eq_nat_mul_zero n

end BedcMathlibBridge.Export.NatMulZero
