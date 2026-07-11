import BedcMathlibBridge.Constructive.NatFactorialPos

namespace BedcMathlibBridge.Export.NatFactorialPos

open BedcMathlibBridge.Constructive.NatFactorialPos

structure NatFactorialPosExportWitness where
  readback : forall n : Nat, 0 < n.factorial
  readback_apply : forall n : Nat, readback n = factorialPosReadback n
  mathlib_apply : forall n : Nat, readback n = Nat.factorial_pos n
  mathlib_anchor : forall n : Nat, 0 < n.factorial
  mathlib_anchor_apply : forall n : Nat, mathlib_anchor n = Nat.factorial_pos n

def natFactorialPosExport : NatFactorialPosExportWitness where
  readback := factorialPosReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := factorialPosReadback_eq_nat_factorial_pos
  mathlib_anchor := Nat.factorial_pos
  mathlib_anchor_apply := by
    intro n
    rfl

theorem nat_factorial_pos_mathlib_correspondence (n : Nat) :
    factorialPosReadback n = Nat.factorial_pos n := by
  exact factorialPosReadback_eq_nat_factorial_pos n

end BedcMathlibBridge.Export.NatFactorialPos
