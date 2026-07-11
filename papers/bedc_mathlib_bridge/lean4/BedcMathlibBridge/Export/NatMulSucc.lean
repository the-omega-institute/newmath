import BedcMathlibBridge.Constructive.NatMulSucc

namespace BedcMathlibBridge.Export.NatMulSucc

open BedcMathlibBridge.Constructive.NatMulSucc

structure NatMulSuccExportWitness where
  readback : ∀ n m : Nat, n * m.succ = n * m + n
  readback_apply : ∀ n m : Nat, readback n m = mulSuccReadback n m
  mathlib_apply : ∀ n m : Nat, readback n m = Nat.mul_succ n m
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natMulSuccExport : NatMulSuccExportWitness where
  readback := mulSuccReadback
  readback_apply := by
    intro n m
    rfl
  mathlib_apply := mulSuccReadback_eq_nat_mul_succ
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_mul_succ_mathlib_correspondence (n m : Nat) :
    mulSuccReadback n m = Nat.mul_succ n m := by
  exact mulSuccReadback_eq_nat_mul_succ n m

end BedcMathlibBridge.Export.NatMulSucc
