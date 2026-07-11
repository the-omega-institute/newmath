import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.NatChooseSuccSelf

private def mathlibNatChooseSuccSelfProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.choose n n.succ = 0 := Nat.choose_succ_self
  ()

def chooseSuccSelfReadback (n : Nat) : Nat.choose n n.succ = 0 :=
  let _ := mathlibNatChooseSuccSelfProvenanceAnchor
  Nat.choose_succ_self n

theorem chooseSuccSelfReadback_eq_nat_choose_succ_self (n : Nat) :
    chooseSuccSelfReadback n = Nat.choose_succ_self n := by
  rfl

end BedcMathlibBridge.Constructive.NatChooseSuccSelf
