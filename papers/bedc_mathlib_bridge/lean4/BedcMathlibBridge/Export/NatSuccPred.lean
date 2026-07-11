import BedcMathlibBridge.Constructive.NatSuccPred

namespace BedcMathlibBridge.Export.NatSuccPred

open BedcMathlibBridge.Constructive.NatSuccPred

structure NatSuccPredExportWitness where
  readback : ∀ {n : Nat}, 0 < n → n.pred.succ = n
  readback_apply : ∀ {n : Nat} (h : 0 < n), readback h = succPredReadback h
  mathlib_apply :
    ∀ {n : Nat} (h : 0 < n), readback h = Nat.succ_pred_eq_of_pos h
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natSuccPredExport : NatSuccPredExportWitness where
  readback := succPredReadback
  readback_apply := by
    intro n h
    rfl
  mathlib_apply := succPredReadback_eq_nat_succ_pred_eq_of_pos
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_succ_pred_mathlib_correspondence {n : Nat} (h : 0 < n) :
    succPredReadback h = Nat.succ_pred_eq_of_pos h := by
  exact succPredReadback_eq_nat_succ_pred_eq_of_pos h

end BedcMathlibBridge.Export.NatSuccPred
