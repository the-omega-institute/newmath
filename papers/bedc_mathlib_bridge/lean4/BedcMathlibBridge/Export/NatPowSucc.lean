import BedcMathlibBridge.Constructive.NatPowSucc

namespace BedcMathlibBridge.Export.NatPowSucc

open BedcMathlibBridge.Constructive.NatPowSucc

structure NatPowSuccExportWitness where
  readback : ∀ n m : Nat, n ^ m.succ = n ^ m * n
  readback_apply : ∀ n m : Nat, readback n m = powSuccReadback n m
  mathlib_apply : ∀ n m : Nat, readback n m = Nat.pow_succ n m
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natPowSuccExport : NatPowSuccExportWitness where
  readback := powSuccReadback
  readback_apply := by
    intro n m
    rfl
  mathlib_apply := powSuccReadback_eq_nat_pow_succ
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_pow_succ_mathlib_correspondence (n m : Nat) :
    powSuccReadback n m = Nat.pow_succ n m := by
  exact powSuccReadback_eq_nat_pow_succ n m

end BedcMathlibBridge.Export.NatPowSucc
