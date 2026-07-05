import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.NatSelfLeFactorial

private def mathlibNatSelfLeFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, n ≤ n.factorial := Nat.self_le_factorial
  ()

def selfLeFactorialReadback (n : Nat) : n ≤ n.factorial :=
  let _ := mathlibNatSelfLeFactorialProvenanceAnchor
  Nat.self_le_factorial n

theorem selfLeFactorialReadback_eq_nat_self_le_factorial (n : Nat) :
    selfLeFactorialReadback n = Nat.self_le_factorial n := by
  rfl

end BedcMathlibBridge.Constructive.NatSelfLeFactorial
