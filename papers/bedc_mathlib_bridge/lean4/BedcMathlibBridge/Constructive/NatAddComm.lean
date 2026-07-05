import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatAddComm

private def mathlibNatAddCommProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n m : Nat, n + m = m + n := Nat.add_comm
  ()

def addCommReadback (n m : Nat) : n + m = m + n :=
  let _ := mathlibNatAddCommProvenanceAnchor
  Nat.add_comm n m

theorem addCommReadback_eq_nat_add_comm (n m : Nat) :
    addCommReadback n m = Nat.add_comm n m := by
  rfl

end BedcMathlibBridge.Constructive.NatAddComm
