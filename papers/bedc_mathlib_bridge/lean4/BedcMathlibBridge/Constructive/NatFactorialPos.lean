import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.NatFactorialPos

private def mathlibNatFactorialPosProvenanceAnchor : Unit :=
  let _ : forall n : Nat, 0 < n.factorial := Nat.factorial_pos
  ()

def factorialPosReadback (n : Nat) : 0 < n.factorial :=
  let _ := mathlibNatFactorialPosProvenanceAnchor
  Nat.factorial_pos n

theorem factorialPosReadback_eq_nat_factorial_pos (n : Nat) :
    factorialPosReadback n = Nat.factorial_pos n := by
  rfl

end BedcMathlibBridge.Constructive.NatFactorialPos
