import BedcMathlibBridge.Constructive.NatPowZero

namespace BedcMathlibBridge.Export.NatPowZero

open BedcMathlibBridge.Constructive.NatPowZero

structure NatPowZeroExportWitness where
  readback : ∀ n : Nat, n ^ 0 = 1
  readback_apply : ∀ n : Nat, readback n = powZeroReadback n
  mathlib_apply : ∀ n : Nat, readback n = Nat.pow_zero n
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natPowZeroExport : NatPowZeroExportWitness where
  readback := powZeroReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := powZeroReadback_eq_nat_pow_zero
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_pow_zero_mathlib_correspondence (n : Nat) :
    powZeroReadback n = Nat.pow_zero n := by
  exact powZeroReadback_eq_nat_pow_zero n

end BedcMathlibBridge.Export.NatPowZero
