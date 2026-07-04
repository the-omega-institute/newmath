import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.NatChooseSuccSucc

private def mathlibNatChooseSuccSuccProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat,
      Nat.choose n.succ k.succ = Nat.choose n k + Nat.choose n k.succ :=
    Nat.choose_succ_succ
  ()

def chooseSuccSuccReadback (n k : Nat) :
    Nat.choose n.succ k.succ = Nat.choose n k + Nat.choose n k.succ :=
  let _ := mathlibNatChooseSuccSuccProvenanceAnchor
  Nat.choose_succ_succ n k

theorem chooseSuccSuccReadback_eq_nat_choose_succ_succ (n k : Nat) :
    chooseSuccSuccReadback n k = Nat.choose_succ_succ n k := by
  rfl

end BedcMathlibBridge.Constructive.NatChooseSuccSucc
