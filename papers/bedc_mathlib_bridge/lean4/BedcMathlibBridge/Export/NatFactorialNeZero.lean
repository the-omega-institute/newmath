import BedcMathlibBridge.Constructive.NatFactorialNeZero

namespace BedcMathlibBridge.Export.NatFactorialNeZero

open BedcMathlibBridge.Constructive.NatFactorialNeZero

structure NatFactorialNeZeroExportWitness where
  readback : forall n : Nat, n.factorial ≠ 0
  readback_apply : forall n : Nat, readback n = factorialNeZeroReadback n
  mathlib_apply : forall n : Nat, readback n = Nat.factorial_ne_zero n
  mathlib_anchor : forall n : Nat, n.factorial ≠ 0
  mathlib_anchor_apply : forall n : Nat, mathlib_anchor n = Nat.factorial_ne_zero n

def natFactorialNeZeroExport : NatFactorialNeZeroExportWitness where
  readback := factorialNeZeroReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := factorialNeZeroReadback_eq_nat_factorial_ne_zero
  mathlib_anchor := Nat.factorial_ne_zero
  mathlib_anchor_apply := by
    intro n
    rfl

theorem nat_factorial_ne_zero_mathlib_correspondence (n : Nat) :
    factorialNeZeroReadback n = Nat.factorial_ne_zero n := by
  exact factorialNeZeroReadback_eq_nat_factorial_ne_zero n

end BedcMathlibBridge.Export.NatFactorialNeZero
