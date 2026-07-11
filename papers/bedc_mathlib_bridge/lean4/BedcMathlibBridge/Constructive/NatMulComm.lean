import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatMulComm

private def mathlibNatMulCommProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n m : Nat, n * m = m * n := Nat.mul_comm
  ()

def mulCommReadback (n m : Nat) : n * m = m * n :=
  let _ := mathlibNatMulCommProvenanceAnchor
  Nat.mul_comm n m

theorem mulCommReadback_eq_nat_mul_comm (n m : Nat) :
    mulCommReadback n m = Nat.mul_comm n m := by
  rfl

end BedcMathlibBridge.Constructive.NatMulComm
