import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.NatChooseEqZeroOfLt

private def mathlibNatChooseEqZeroOfLtProvenanceAnchor : Unit :=
  let _ : ∀ {n k : Nat}, n < k → Nat.choose n k = 0 :=
    Nat.choose_eq_zero_of_lt
  ()

def chooseEqZeroOfLtReadback {n k : Nat} (h : n < k) :
    Nat.choose n k = 0 :=
  let _ := mathlibNatChooseEqZeroOfLtProvenanceAnchor
  Nat.choose_eq_zero_of_lt h

theorem chooseEqZeroOfLtReadback_eq_nat_choose_eq_zero_of_lt
    {n k : Nat} (h : n < k) :
    chooseEqZeroOfLtReadback h = Nat.choose_eq_zero_of_lt h := by
  rfl

end BedcMathlibBridge.Constructive.NatChooseEqZeroOfLt
