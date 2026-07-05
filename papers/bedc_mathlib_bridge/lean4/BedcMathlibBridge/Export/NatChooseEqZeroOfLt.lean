import BedcMathlibBridge.Constructive.NatChooseEqZeroOfLt

namespace BedcMathlibBridge.Export.NatChooseEqZeroOfLt

open BedcMathlibBridge.Constructive.NatChooseEqZeroOfLt

structure NatChooseEqZeroOfLtExportWitness where
  readback : {n k : Nat} → n < k → Nat.choose n k = 0
  readback_apply :
    ∀ {n k : Nat} (h : n < k),
      readback h = chooseEqZeroOfLtReadback h
  mathlib_apply :
    ∀ {n k : Nat} (h : n < k),
      readback h = Nat.choose_eq_zero_of_lt h
  mathlib_anchor : {n k : Nat} → n < k → Nat.choose n k = 0
  mathlib_anchor_apply :
    ∀ {n k : Nat} (h : n < k),
      mathlib_anchor h = Nat.choose_eq_zero_of_lt h

def natChooseEqZeroOfLtExport : NatChooseEqZeroOfLtExportWitness where
  readback := chooseEqZeroOfLtReadback
  readback_apply := by
    intro n k h
    rfl
  mathlib_apply := chooseEqZeroOfLtReadback_eq_nat_choose_eq_zero_of_lt
  mathlib_anchor := Nat.choose_eq_zero_of_lt
  mathlib_anchor_apply := by
    intro n k h
    rfl

theorem nat_choose_eq_zero_of_lt_mathlib_correspondence
    {n k : Nat} (h : n < k) :
    chooseEqZeroOfLtReadback h = Nat.choose_eq_zero_of_lt h := by
  exact chooseEqZeroOfLtReadback_eq_nat_choose_eq_zero_of_lt h

end BedcMathlibBridge.Export.NatChooseEqZeroOfLt
