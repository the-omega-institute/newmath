import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_unit_scope [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name leftUnitRead
      rightUnitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      Cont identity hom leftUnitRead →
        Cont hom identity rightUnitRead →
          PkgSig bundle leftUnitRead pkg →
            PkgSig bundle rightUnitRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row leftUnitRead ∨ hsame row rightUnitRead)
                  (fun row : BHist => hsame row identity ∨ hsame row hom ∨ hsame row unit)
                  (fun _row : BHist =>
                    PkgSig bundle leftUnitRead pkg ∨ PkgSig bundle rightUnitRead pkg)
                  hsame ∧
                Cont identity hom leftUnitRead ∧ Cont hom identity rightUnitRead ∧
                  hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier leftUnitRoute rightUnitRoute leftPkg rightPkg
  obtain ⟨_objectUnary, identityCarrier, _identityCompositionHom, _associativitySame,
    unitSame, nameSame⟩ := carrier
  have identityEmpty : hsame identity BHist.Empty :=
    (CategoryHomCarrier_endomorphism_empty_iff.mp identityCarrier).right
  have leftSameHom : hsame leftUnitRead hom := by
    cases identityEmpty
    exact cont_left_unit_result leftUnitRoute
  have rightSameHom : hsame rightUnitRead hom := by
    cases identityEmpty
    exact cont_deterministic rightUnitRoute (cont_right_unit hom)
  have sourceLeft :
      (fun row : BHist => hsame row leftUnitRead ∨ hsame row rightUnitRead)
        leftUnitRead := by
    exact Or.inl (hsame_refl leftUnitRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row leftUnitRead ∨ hsame row rightUnitRead)
          (fun row : BHist => hsame row identity ∨ hsame row hom ∨ hsame row unit)
          (fun _row : BHist =>
            PkgSig bundle leftUnitRead pkg ∨ PkgSig bundle rightUnitRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro leftUnitRead sourceLeft
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
          cases source with
          | inl sameLeft =>
              exact Or.inl (hsame_trans (hsame_symm same) sameLeft)
          | inr sameRight =>
              exact Or.inr (hsame_trans (hsame_symm same) sameRight)
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl sameLeft =>
            exact Or.inr (Or.inl (hsame_trans sameLeft leftSameHom))
        | inr sameRight =>
            exact Or.inr (Or.inl (hsame_trans sameRight rightSameHom))
      ledger_sound := by
        intro _row source
        cases source with
        | inl _sameLeft =>
            exact Or.inl leftPkg
        | inr _sameRight =>
            exact Or.inr rightPkg
    }
  exact ⟨cert, leftUnitRoute, rightUnitRoute, unitSame, nameSame⟩

end BEDC.Derived.KernelCategoryUp
