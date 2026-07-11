import BedcMathlibBridge.Constructive.NatMulComm

namespace BedcMathlibBridge.Export.NatMulComm

open BedcMathlibBridge.Constructive.NatMulComm

structure NatMulCommExportWitness where
  readback : ∀ n m : Nat, n * m = m * n
  readback_apply : ∀ n m : Nat, readback n m = mulCommReadback n m
  mathlib_apply : ∀ n m : Nat, readback n m = Nat.mul_comm n m
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natMulCommExport : NatMulCommExportWitness where
  readback := mulCommReadback
  readback_apply := by
    intro n m
    rfl
  mathlib_apply := mulCommReadback_eq_nat_mul_comm
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_mul_comm_mathlib_correspondence (n m : Nat) :
    mulCommReadback n m = Nat.mul_comm n m := by
  exact mulCommReadback_eq_nat_mul_comm n m

end BedcMathlibBridge.Export.NatMulComm
