import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.NatFactorialNeZero

private def mathlibNatFactorialNeZeroProvenanceAnchor : Unit :=
  let _ : forall n : Nat, n.factorial ≠ 0 := Nat.factorial_ne_zero
  ()

def factorialNeZeroReadback (n : Nat) : n.factorial ≠ 0 :=
  let _ := mathlibNatFactorialNeZeroProvenanceAnchor
  Nat.factorial_ne_zero n

theorem factorialNeZeroReadback_eq_nat_factorial_ne_zero (n : Nat) :
    factorialNeZeroReadback n = Nat.factorial_ne_zero n := by
  rfl

end BedcMathlibBridge.Constructive.NatFactorialNeZero
