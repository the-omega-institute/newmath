import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelCategoryCarrier_law_transport_exhaustion
    {object hom identity composition associativity unit provenance name lawRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      Cont associativity unit lawRead ->
        hsame associativity (append hom composition) ∧ hsame unit identity ∧
          hsame name (append provenance unit) ∧
            SemanticNameCert
              (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
              (fun row : BHist =>
                hsame row lawRead ∧ hsame associativity (append hom composition))
              (fun row : BHist =>
                hsame row lawRead ∧ hsame unit identity ∧
                  hsame name (append provenance unit))
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier lawRoute
  obtain ⟨_objectUnary, _identityCarrier, _identityCompositionHom, associativitySame,
    unitSame, nameSame⟩ := carrier
  have sourceLaw :
      (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead) lawRead := by
    exact ⟨hsame_refl lawRead, lawRoute⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        (fun row : BHist =>
          hsame row lawRead ∧ hsame associativity (append hom composition))
        (fun row : BHist =>
          hsame row lawRead ∧ hsame unit identity ∧ hsame name (append provenance unit))
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lawRead sourceLaw
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, associativitySame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, unitSame, nameSame⟩
    }
  exact ⟨associativitySame, unitSame, nameSame, cert⟩

end BEDC.Derived.KernelCategoryUp
