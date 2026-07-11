import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatMulOne

private def mathlibNatMulOneProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall n : Nat, n * 1 = n := Nat.mul_one
  ()

def mulOneReadback (n : Nat) : n * 1 = n :=
  let _ := mathlibNatMulOneProvenanceAnchor
  Nat.mul_one n

theorem mulOneReadback_eq_nat_mul_one (n : Nat) :
    mulOneReadback n = Nat.mul_one n := by
  rfl

end BedcMathlibBridge.Constructive.NatMulOne
