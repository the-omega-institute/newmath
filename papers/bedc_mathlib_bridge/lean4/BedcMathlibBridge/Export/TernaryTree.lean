import BedcMathlibBridge.Constructive.TernaryTree

namespace BedcMathlibBridge.Export.TernaryTree

open BedcMathlibBridge.Constructive.TernaryTree

structure TernaryTreeExportWitness where
  readback : Nat -> Nat
  readback_apply :
    forall n : Nat, readback n = toNat n
  bedc_apply :
    forall n : Nat,
      readback n = BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 n
  nat_choose_initial_formula :
    readback 0 = Nat.choose (3 * 0) 0 / ((3 - 1) * 0 + 1) ∧
      readback 1 = Nat.choose (3 * 1) 1 / ((3 - 1) * 1 + 1) ∧
      readback 2 = Nat.choose (3 * 2) 2 / ((3 - 1) * 2 + 1) ∧
      readback 3 = Nat.choose (3 * 3) 3 / ((3 - 1) * 3 + 1)
  initial_values :
    readback 0 = 1 ∧ readback 1 = 1 ∧ readback 2 = 3 ∧ readback 3 = 12

def ternaryTreeExport : TernaryTreeExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  nat_choose_initial_formula := toNat_ternary_initial_choose_formula
  initial_values := toNat_initial_values

theorem ternaryTree_initial_choose_formula :
    BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 0 =
        Nat.choose (3 * 0) 0 / ((3 - 1) * 0 + 1) ∧
      BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 1 =
        Nat.choose (3 * 1) 1 / ((3 - 1) * 1 + 1) ∧
      BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 2 =
        Nat.choose (3 * 2) 2 / ((3 - 1) * 2 + 1) ∧
      BEDC.Derived.FussCatalanUp.treeFussCatalanCount 3 3 =
        Nat.choose (3 * 3) 3 / ((3 - 1) * 3 + 1) :=
  BedcMathlibBridge.Constructive.TernaryTree.treeFussCatalanCount_ternary_initial_choose_formula

end BedcMathlibBridge.Export.TernaryTree
