import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.NatFactorialZero

private def mathlibNatFactorialZeroProvenanceAnchor : Unit :=
  let _ : Nat.factorial 0 = 1 := Nat.factorial_zero
  ()

def factorialZeroReadback : Nat.factorial 0 = 1 :=
  let _ := mathlibNatFactorialZeroProvenanceAnchor
  Nat.factorial_zero

theorem factorialZeroReadback_eq_nat_factorial_zero :
    factorialZeroReadback = Nat.factorial_zero := by
  rfl

end BedcMathlibBridge.Constructive.NatFactorialZero
