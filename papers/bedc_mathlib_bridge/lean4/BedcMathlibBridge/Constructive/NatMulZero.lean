import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatMulZero

private def mathlibNatMulZeroProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n : Nat, n * 0 = 0 := Nat.mul_zero
  ()

def mulZeroReadback (n : Nat) : n * 0 = 0 :=
  let _ := mathlibNatMulZeroProvenanceAnchor
  Nat.mul_zero n

theorem mulZeroReadback_eq_nat_mul_zero (n : Nat) :
    mulZeroReadback n = Nat.mul_zero n := by
  rfl

end BedcMathlibBridge.Constructive.NatMulZero
