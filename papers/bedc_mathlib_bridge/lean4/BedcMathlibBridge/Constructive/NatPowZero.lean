import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatPowZero

private def mathlibNatPowZeroProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n : Nat, n ^ 0 = 1 := Nat.pow_zero
  ()

def powZeroReadback (n : Nat) : n ^ 0 = 1 :=
  let _ := mathlibNatPowZeroProvenanceAnchor
  Nat.pow_zero n

theorem powZeroReadback_eq_nat_pow_zero (n : Nat) :
    powZeroReadback n = Nat.pow_zero n := by
  rfl

end BedcMathlibBridge.Constructive.NatPowZero
