import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ModuleForgetsAbgroupCertificate :
    SemanticNameCert ModuleSingletonCarrier
        (fun row : BHist =>
          ModuleSingletonCarrier row \/
            (exists x : BHist, exists y : BHist,
              ModuleSingletonCarrier x /\ ModuleSingletonCarrier y /\
                hsame row (ModuleSingletonAdd x y)) \/
              (exists x : BHist,
                ModuleSingletonCarrier x /\ hsame row (ModuleSingletonNeg x)) \/
                hsame row ModuleSingletonZero)
        ModuleSingletonCarrier ModuleSingletonClassifier /\
      ModuleSingletonCarrier ModuleSingletonZero := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert ModuleSingletonCarrier
  have zeroCarrier : ModuleSingletonCarrier ModuleSingletonZero := hsame_refl BHist.Empty
  have cert :
      SemanticNameCert ModuleSingletonCarrier
          (fun row : BHist =>
            ModuleSingletonCarrier row \/
              (exists x : BHist, exists y : BHist,
                ModuleSingletonCarrier x /\ ModuleSingletonCarrier y /\
                  hsame row (ModuleSingletonAdd x y)) \/
                (exists x : BHist,
                  ModuleSingletonCarrier x /\ hsame row (ModuleSingletonNeg x)) \/
                  hsame row ModuleSingletonZero)
          ModuleSingletonCarrier ModuleSingletonClassifier := {
    core := {
      carrier_inhabited := Exists.intro ModuleSingletonZero zeroCarrier
      equiv_refl := by
        intro row carrier
        exact ⟨carrier, carrier, hsame_refl row⟩
      equiv_symm := by
        intro _row _other sameRows
        exact ⟨sameRows.right.left, sameRows.left, hsame_symm sameRows.right.right⟩
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact
          ⟨sameLeft.left, sameRight.right.left,
            hsame_trans sameLeft.right.right sameRight.right.right⟩
      carrier_respects_equiv := by
        intro _row _other sameRows _carrier
        exact sameRows.right.left
    }
    pattern_sound := by
      intro _row source
      exact Or.inl source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨cert, zeroCarrier⟩

end BEDC.Derived.ModuleUp
