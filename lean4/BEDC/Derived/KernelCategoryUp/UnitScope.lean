import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem KernelCategoryUnitScope
    {object hom identity composition associativity unit provenance name unitRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      hsame unitRead unit ->
        SemanticNameCert
            (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row unitRead ∧ hsame unit identity)
            (fun row : BHist =>
              hsame row unitRead ∧ hsame name (append provenance unit))
            hsame ∧
          UnaryHistory unitRead ∧ hsame unitRead identity ∧ hsame unit identity ∧
            hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier sameUnitRead
  obtain ⟨_objectUnary, identityCarrier, _compositionRoute, _associativitySame,
    unitSame, nameSame⟩ := carrier
  have identityUnary : UnaryHistory identity :=
    identityCarrier.right.right.left
  have unitReadIdentity : hsame unitRead identity :=
    hsame_trans sameUnitRead unitSame
  have unitReadUnary : UnaryHistory unitRead :=
    unary_transport identityUnary (hsame_symm unitReadIdentity)
  have sourceUnitRead :
      (fun row : BHist => hsame row unitRead ∧ UnaryHistory row) unitRead := by
    exact ⟨hsame_refl unitRead, unitReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row unitRead ∧ hsame unit identity)
          (fun row : BHist =>
            hsame row unitRead ∧ hsame name (append provenance unit))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro unitRead sourceUnitRead
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, unitSame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, nameSame⟩
    }
  exact ⟨cert, unitReadUnary, unitReadIdentity, unitSame, nameSame⟩

end BEDC.Derived.KernelCategoryUp
