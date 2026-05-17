import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_downstream_namecert_readiness
    {object hom identity composition associativity unit provenance name downstreamRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      UnaryHistory composition →
        Cont hom composition downstreamRead →
          SemanticNameCert
              (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row downstreamRead ∧ Cont identity composition hom ∧
                  Cont hom composition downstreamRead)
              (fun row : BHist => hsame row downstreamRead ∧ hsame name (append provenance unit))
              hsame ∧
            UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
              UnaryHistory hom ∧ UnaryHistory downstreamRead ∧ Cont identity composition hom ∧
                Cont hom composition downstreamRead ∧ hsame associativity (append hom composition) ∧
                  hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert CategoryHomCarrier
  intro carrier compositionUnary downstreamRoute
  obtain ⟨objectUnary, identityCarrier, identityCompositionHom, associativitySame,
    unitSame, nameSame⟩ := carrier
  have identityUnary : UnaryHistory identity :=
    identityCarrier.right.right.left
  have homUnary : UnaryHistory hom :=
    unary_cont_closed identityUnary compositionUnary identityCompositionHom
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed homUnary compositionUnary downstreamRoute
  have sourceDownstream :
      (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row) downstreamRead := by
    exact ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont identity composition hom ∧
              Cont hom composition downstreamRead)
          (fun row : BHist => hsame row downstreamRead ∧ hsame name (append provenance unit))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro downstreamRead sourceDownstream
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
          intro row other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨source.left,
            identityCompositionHom,
            downstreamRoute⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, nameSame⟩
    }
  exact
    ⟨cert, objectUnary, identityCarrier, homUnary, downstreamUnary, identityCompositionHom,
      downstreamRoute, associativitySame, unitSame, nameSame⟩

end BEDC.Derived.KernelCategoryUp
