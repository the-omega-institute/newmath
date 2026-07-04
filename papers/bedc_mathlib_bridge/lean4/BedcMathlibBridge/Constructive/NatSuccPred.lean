import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatSuccPred

private def mathlibNatSuccPredProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ {n : Nat}, 0 < n → n.pred.succ = n :=
    Nat.succ_pred_eq_of_pos
  ()

def succPredReadback {n : Nat} (h : 0 < n) : n.pred.succ = n :=
  let _ := mathlibNatSuccPredProvenanceAnchor
  Nat.succ_pred_eq_of_pos h

theorem succPredReadback_eq_nat_succ_pred_eq_of_pos {n : Nat} (h : 0 < n) :
    succPredReadback h = Nat.succ_pred_eq_of_pos h := by
  rfl

end BedcMathlibBridge.Constructive.NatSuccPred
