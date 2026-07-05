import BedcMathlibBridge.Constructive.NatChooseSuccSelf

namespace BedcMathlibBridge.Export.NatChooseSuccSelf

open BedcMathlibBridge.Constructive.NatChooseSuccSelf

structure NatChooseSuccSelfExportWitness where
  readback : ∀ n : Nat, Nat.choose n n.succ = 0
  readback_apply : ∀ n : Nat, readback n = chooseSuccSelfReadback n
  mathlib_apply : ∀ n : Nat, readback n = Nat.choose_succ_self n
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natChooseSuccSelfExport : NatChooseSuccSelfExportWitness where
  readback := chooseSuccSelfReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := chooseSuccSelfReadback_eq_nat_choose_succ_self
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_choose_succ_self_mathlib_correspondence (n : Nat) :
    chooseSuccSelfReadback n = Nat.choose_succ_self n := by
  exact chooseSuccSelfReadback_eq_nat_choose_succ_self n

end BedcMathlibBridge.Export.NatChooseSuccSelf
