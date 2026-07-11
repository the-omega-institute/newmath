import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatMulSucc

private def mathlibNatMulSuccProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n m : Nat, n * m.succ = n * m + n := Nat.mul_succ
  ()

def mulSuccReadback (n m : Nat) : n * m.succ = n * m + n :=
  let _ := mathlibNatMulSuccProvenanceAnchor
  Nat.mul_succ n m

theorem mulSuccReadback_eq_nat_mul_succ (n m : Nat) :
    mulSuccReadback n m = Nat.mul_succ n m := by
  rfl

end BedcMathlibBridge.Constructive.NatMulSucc
