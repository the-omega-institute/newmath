import BedcMathlibBridge.Constructive.NatChooseZeroRight

namespace BedcMathlibBridge.Export.NatChooseZeroRight

open BedcMathlibBridge.Constructive.NatChooseZeroRight

structure NatChooseZeroRightExportWitness where
  readback : ∀ n : Nat, Nat.choose n 0 = 1
  readback_apply : ∀ n : Nat, readback n = chooseZeroRightReadback n
  mathlib_apply : ∀ n : Nat, readback n = Nat.choose_zero_right n
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natChooseZeroRightExport : NatChooseZeroRightExportWitness where
  readback := chooseZeroRightReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := chooseZeroRightReadback_eq_nat_choose_zero_right
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_choose_zero_right_mathlib_correspondence (n : Nat) :
    chooseZeroRightReadback n = Nat.choose_zero_right n := by
  exact chooseZeroRightReadback_eq_nat_choose_zero_right n

end BedcMathlibBridge.Export.NatChooseZeroRight
