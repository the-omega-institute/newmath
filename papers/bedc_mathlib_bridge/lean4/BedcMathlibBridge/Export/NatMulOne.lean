import BedcMathlibBridge.Constructive.NatMulOne

namespace BedcMathlibBridge.Export.NatMulOne

open BedcMathlibBridge.Constructive.NatMulOne

structure NatMulOneExportWitness where
  readback : forall n : Nat, n * 1 = n
  readback_apply : forall n : Nat, readback n = mulOneReadback n
  mathlib_apply : forall n : Nat, readback n = Nat.mul_one n
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natMulOneExport : NatMulOneExportWitness where
  readback := mulOneReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := mulOneReadback_eq_nat_mul_one
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_mul_one_mathlib_correspondence (n : Nat) :
    mulOneReadback n = Nat.mul_one n := by
  exact mulOneReadback_eq_nat_mul_one n

end BedcMathlibBridge.Export.NatMulOne
