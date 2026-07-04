import BedcMathlibBridge.Constructive.NatChooseSuccSucc

namespace BedcMathlibBridge.Export.NatChooseSuccSucc

open BedcMathlibBridge.Constructive.NatChooseSuccSucc

structure NatChooseSuccSuccExportWitness where
  readback :
    ∀ n k : Nat,
      Nat.choose n.succ k.succ = Nat.choose n k + Nat.choose n k.succ
  readback_apply :
    ∀ n k : Nat, readback n k = chooseSuccSuccReadback n k
  mathlib_apply :
    ∀ n k : Nat, readback n k = Nat.choose_succ_succ n k
  mathlib_anchor :
    ∀ n k : Nat,
      Nat.choose n.succ k.succ = Nat.choose n k + Nat.choose n k.succ
  mathlib_anchor_apply :
    ∀ n k : Nat, mathlib_anchor n k = Nat.choose_succ_succ n k

def natChooseSuccSuccExport : NatChooseSuccSuccExportWitness where
  readback := chooseSuccSuccReadback
  readback_apply := by
    intro n k
    rfl
  mathlib_apply := chooseSuccSuccReadback_eq_nat_choose_succ_succ
  mathlib_anchor := Nat.choose_succ_succ
  mathlib_anchor_apply := by
    intro n k
    rfl

theorem nat_choose_succ_succ_mathlib_correspondence (n k : Nat) :
    chooseSuccSuccReadback n k = Nat.choose_succ_succ n k := by
  exact chooseSuccSuccReadback_eq_nat_choose_succ_succ n k

end BedcMathlibBridge.Export.NatChooseSuccSucc
