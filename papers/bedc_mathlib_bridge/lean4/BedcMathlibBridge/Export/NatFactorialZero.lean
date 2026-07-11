import BedcMathlibBridge.Constructive.NatFactorialZero

namespace BedcMathlibBridge.Export.NatFactorialZero

open BedcMathlibBridge.Constructive.NatFactorialZero

structure NatFactorialZeroExportWitness where
  readback : Nat.factorial 0 = 1
  readback_apply : readback = factorialZeroReadback
  mathlib_apply : readback = Nat.factorial_zero
  mathlib_anchor : Nat.factorial 0 = 1
  mathlib_anchor_apply : mathlib_anchor = Nat.factorial_zero

def natFactorialZeroExport : NatFactorialZeroExportWitness where
  readback := factorialZeroReadback
  readback_apply := by
    rfl
  mathlib_apply := factorialZeroReadback_eq_nat_factorial_zero
  mathlib_anchor := Nat.factorial_zero
  mathlib_anchor_apply := by
    rfl

theorem nat_factorial_zero_mathlib_correspondence :
    factorialZeroReadback = Nat.factorial_zero := by
  exact factorialZeroReadback_eq_nat_factorial_zero

end BedcMathlibBridge.Export.NatFactorialZero
