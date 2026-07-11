import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatPowSucc

private def mathlibNatPowSuccProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n m : Nat, n ^ m.succ = n ^ m * n := Nat.pow_succ
  ()

def powSuccReadback (n m : Nat) : n ^ m.succ = n ^ m * n :=
  let _ := mathlibNatPowSuccProvenanceAnchor
  Nat.pow_succ n m

theorem powSuccReadback_eq_nat_pow_succ (n m : Nat) :
    powSuccReadback n m = Nat.pow_succ n m := by
  rfl

end BedcMathlibBridge.Constructive.NatPowSucc
