import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatOneMul

private def mathlibNatOneMulProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall n : Nat, 1 * n = n := Nat.one_mul
  ()

def oneMulReadback (n : Nat) : 1 * n = n :=
  let _ := mathlibNatOneMulProvenanceAnchor
  Nat.one_mul n

theorem oneMulReadback_eq_nat_one_mul (n : Nat) :
    oneMulReadback n = Nat.one_mul n := by
  rfl

end BedcMathlibBridge.Constructive.NatOneMul
