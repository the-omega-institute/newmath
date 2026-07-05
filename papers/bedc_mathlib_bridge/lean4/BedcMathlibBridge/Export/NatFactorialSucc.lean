import BedcMathlibBridge.Constructive.NatFactorialSucc

namespace BedcMathlibBridge.Export.NatFactorialSucc

open BedcMathlibBridge.Constructive.NatFactorialSucc

structure NatFactorialSuccExportWitness where
  readback : ∀ n : Nat, (n + 1).factorial = (n + 1) * n.factorial
  readback_apply : ∀ n : Nat, readback n = factorialSuccReadback n
  mathlib_apply : ∀ n : Nat, readback n = Nat.factorial_succ n
  mathlib_anchor : ∀ n : Nat, (n + 1).factorial = (n + 1) * n.factorial
  mathlib_anchor_apply : ∀ n : Nat, mathlib_anchor n = Nat.factorial_succ n

def natFactorialSuccExport : NatFactorialSuccExportWitness where
  readback := factorialSuccReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := factorialSuccReadback_eq_nat_factorial_succ
  mathlib_anchor := Nat.factorial_succ
  mathlib_anchor_apply := by
    intro n
    rfl

theorem nat_factorial_succ_mathlib_correspondence (n : Nat) :
    factorialSuccReadback n = Nat.factorial_succ n := by
  exact factorialSuccReadback_eq_nat_factorial_succ n

end BedcMathlibBridge.Export.NatFactorialSucc
