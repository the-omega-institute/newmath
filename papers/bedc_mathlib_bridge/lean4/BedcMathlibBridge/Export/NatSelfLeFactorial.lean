import BedcMathlibBridge.Constructive.NatSelfLeFactorial

namespace BedcMathlibBridge.Export.NatSelfLeFactorial

open BedcMathlibBridge.Constructive.NatSelfLeFactorial

structure NatSelfLeFactorialExportWitness where
  readback : ∀ n : Nat, n ≤ n.factorial
  readback_apply : ∀ n : Nat, readback n = selfLeFactorialReadback n
  mathlib_apply : ∀ n : Nat, readback n = Nat.self_le_factorial n
  mathlib_anchor : ∀ n : Nat, n ≤ n.factorial
  mathlib_anchor_apply : ∀ n : Nat, mathlib_anchor n = Nat.self_le_factorial n

def natSelfLeFactorialExport : NatSelfLeFactorialExportWitness where
  readback := selfLeFactorialReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := selfLeFactorialReadback_eq_nat_self_le_factorial
  mathlib_anchor := Nat.self_le_factorial
  mathlib_anchor_apply := by
    intro n
    rfl

theorem nat_self_le_factorial_mathlib_correspondence (n : Nat) :
    selfLeFactorialReadback n = Nat.self_le_factorial n := by
  exact selfLeFactorialReadback_eq_nat_self_le_factorial n

end BedcMathlibBridge.Export.NatSelfLeFactorial
