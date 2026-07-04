import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatAddAssoc

private def mathlibNatAddAssocProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : ∀ n m k : Nat, n + m + k = n + (m + k) := Nat.add_assoc
  ()

def addAssocReadback (n m k : Nat) : n + m + k = n + (m + k) :=
  let _ := mathlibNatAddAssocProvenanceAnchor
  Nat.add_assoc n m k

theorem addAssocReadback_eq_nat_add_assoc (n m k : Nat) :
    addAssocReadback n m k = Nat.add_assoc n m k := by
  rfl

end BedcMathlibBridge.Constructive.NatAddAssoc
