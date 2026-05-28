import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelCategoryUp_StdBridge
    {object hom identity composition associativity unit provenance name : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row name ∧
              KernelCategoryCarrier object hom identity composition associativity unit
                provenance name)
          (fun row : BHist => hsame row name ∧ Cont identity composition hom)
          (fun row : BHist =>
            hsame row name ∧ hsame unit identity ∧
              hsame associativity (append hom composition))
          hsame ∧
        KernelCategoryCarrier object hom identity composition associativity unit provenance
          name := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier
  have carrierPacket :
      KernelCategoryCarrier object hom identity composition associativity unit provenance
        name := carrier
  obtain ⟨_objectUnary, _identityCarrier, compositionRoute, associativitySame, unitSame,
    _nameSame⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row name ∧
              KernelCategoryCarrier object hom identity composition associativity unit
                provenance name)
          (fun row : BHist => hsame row name ∧ Cont identity composition hom)
          (fun row : BHist =>
            hsame row name ∧ hsame unit identity ∧
              hsame associativity (append hom composition))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, carrierPacket⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, compositionRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, unitSame, associativitySame⟩
  }
  exact ⟨cert, carrierPacket⟩

end BEDC.Derived.KernelCategoryUp
