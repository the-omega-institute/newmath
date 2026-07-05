import BedcMathlibBridge.Constructive.NatAddComm

namespace BedcMathlibBridge.Export.NatAddComm

open BedcMathlibBridge.Constructive.NatAddComm

structure NatAddCommExportWitness where
  readback : ∀ n m : Nat, n + m = m + n
  readback_apply : ∀ n m : Nat, readback n m = addCommReadback n m
  mathlib_apply : ∀ n m : Nat, readback n m = Nat.add_comm n m
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natAddCommExport : NatAddCommExportWitness where
  readback := addCommReadback
  readback_apply := by
    intro n m
    rfl
  mathlib_apply := addCommReadback_eq_nat_add_comm
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_add_comm_mathlib_correspondence (n m : Nat) :
    addCommReadback n m = Nat.add_comm n m := by
  exact addCommReadback_eq_nat_add_comm n m

end BedcMathlibBridge.Export.NatAddComm
