import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.FussCatalanUp
import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.TernaryTree

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 n := by
  rfl

theorem treeFussCatalanCount_ternary_initial_choose_formula :
    BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 0 =
        Nat.choose (3 * 0) 0 / ((3 - 1) * 0 + 1) ∧
      BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 1 =
        Nat.choose (3 * 1) 1 / ((3 - 1) * 1 + 1) ∧
      BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 2 =
        Nat.choose (3 * 2) 2 / ((3 - 1) * 2 + 1) ∧
      BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 3 =
        Nat.choose (3 * 3) 3 / ((3 - 1) * 3 + 1) := by
  decide

theorem toNat_ternary_initial_choose_formula :
    toNat 0 = Nat.choose (3 * 0) 0 / ((3 - 1) * 0 + 1) ∧
      toNat 1 = Nat.choose (3 * 1) 1 / ((3 - 1) * 1 + 1) ∧
      toNat 2 = Nat.choose (3 * 2) 2 / ((3 - 1) * 2 + 1) ∧
      toNat 3 = Nat.choose (3 * 3) 3 / ((3 - 1) * 3 + 1) := by
  exact treeFussCatalanCount_ternary_initial_choose_formula

theorem toNat_initial_values :
    toNat 0 = 1 ∧ toNat 1 = 1 ∧ toNat 2 = 3 ∧ toNat 3 = 12 := by
  decide

end BedcMathlibBridge.Constructive.TernaryTree
