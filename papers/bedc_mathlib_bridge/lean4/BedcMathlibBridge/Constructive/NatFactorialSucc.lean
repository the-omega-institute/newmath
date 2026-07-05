import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.NatFactorialSucc

private def mathlibNatFactorialSuccProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, (n + 1).factorial = (n + 1) * n.factorial :=
    Nat.factorial_succ
  ()

def factorialSuccReadback (n : Nat) :
    (n + 1).factorial = (n + 1) * n.factorial :=
  let _ := mathlibNatFactorialSuccProvenanceAnchor
  Nat.factorial_succ n

theorem factorialSuccReadback_eq_nat_factorial_succ (n : Nat) :
    factorialSuccReadback n = Nat.factorial_succ n := by
  rfl

end BedcMathlibBridge.Constructive.NatFactorialSucc
