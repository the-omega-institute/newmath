import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NatSuccInjective

private def mathlibNatSuccInjectiveProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def succInjectiveReadback : Function.Injective Nat.succ :=
  let _ := mathlibNatSuccInjectiveProvenanceAnchor
  Nat.succ_injective

theorem succInjectiveReadback_eq_nat_succ_injective :
    succInjectiveReadback = Nat.succ_injective := by
  rfl

end BedcMathlibBridge.Constructive.NatSuccInjective
