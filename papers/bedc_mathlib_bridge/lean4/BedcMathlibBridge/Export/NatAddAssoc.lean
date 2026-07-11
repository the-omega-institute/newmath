import BedcMathlibBridge.Constructive.NatAddAssoc

namespace BedcMathlibBridge.Export.NatAddAssoc

open BedcMathlibBridge.Constructive.NatAddAssoc

structure NatAddAssocExportWitness where
  readback : ∀ n m k : Nat, n + m + k = n + (m + k)
  readback_apply : ∀ n m k : Nat, readback n m k = addAssocReadback n m k
  mathlib_apply : ∀ n m k : Nat, readback n m k = Nat.add_assoc n m k
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natAddAssocExport : NatAddAssocExportWitness where
  readback := addAssocReadback
  readback_apply := by
    intro n m k
    rfl
  mathlib_apply := addAssocReadback_eq_nat_add_assoc
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_add_assoc_mathlib_correspondence (n m k : Nat) :
    addAssocReadback n m k = Nat.add_assoc n m k := by
  exact addAssocReadback_eq_nat_add_assoc n m k

end BedcMathlibBridge.Export.NatAddAssoc
