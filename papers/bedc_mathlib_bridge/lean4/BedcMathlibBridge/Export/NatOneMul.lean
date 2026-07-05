import BedcMathlibBridge.Constructive.NatOneMul

namespace BedcMathlibBridge.Export.NatOneMul

open BedcMathlibBridge.Constructive.NatOneMul

structure NatOneMulExportWitness where
  readback : forall n : Nat, 1 * n = n
  readback_apply : forall n : Nat, readback n = oneMulReadback n
  mathlib_apply : forall n : Nat, readback n = Nat.one_mul n
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natOneMulExport : NatOneMulExportWitness where
  readback := oneMulReadback
  readback_apply := by
    intro n
    rfl
  mathlib_apply := oneMulReadback_eq_nat_one_mul
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_one_mul_mathlib_correspondence (n : Nat) :
    oneMulReadback n = Nat.one_mul n := by
  exact oneMulReadback_eq_nat_one_mul n

end BedcMathlibBridge.Export.NatOneMul
