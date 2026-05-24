import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_composition_cont_route_exactness
    {object hom identity composition associativity unit provenance name a b c f g fg routeRead :
      BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      CategoryHomCarrier a b f →
        CategoryHomCarrier b c g →
          Cont f g fg →
            UnaryHistory name →
              Cont fg name routeRead →
                CategoryHomCarrier a c fg ∧ UnaryHistory routeRead ∧ Cont f g fg ∧
                  Cont fg name routeRead ∧ hsame associativity (append hom composition) ∧
                    hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CategoryHomCarrier
  intro carrier left right comp nameUnary fgNameRoute
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have fgUnary : UnaryHistory fg := composite.right.right.left
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed fgUnary nameUnary fgNameRoute
  exact
    ⟨composite, routeReadUnary, comp, fgNameRoute, carrier.right.right.right.left,
      carrier.right.right.right.right.left, carrier.right.right.right.right.right⟩

theorem KernelCategoryCarrier_cont_composition_locality [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name a b c f g fg
      lawRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      CategoryHomCarrier a b f →
        CategoryHomCarrier b c g →
          Cont f g fg →
            Cont associativity unit lawRead →
              PkgSig bundle lawRead pkg →
                CategoryHomCarrier a c fg ∧ Cont f g fg ∧
                  hsame associativity (append hom composition) ∧ hsame unit identity ∧
                    hsame name (append provenance unit) ∧
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row lawRead ∧ Cont associativity unit lawRead)
                        (fun row : BHist => hsame row lawRead ∧ Cont f g fg)
                        (fun row : BHist => hsame row lawRead ∧ PkgSig bundle lawRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert CategoryHomCarrier PkgSig
  intro carrier left right comp lawRoute lawPkg
  have compositionData :
      CategoryHomCarrier a c fg ∧ hsame associativity (append hom composition) ∧
        hsame unit identity ∧ hsame name (append provenance unit) :=
    KernelCategoryCarrier_composition_continuation carrier left right comp
  have sourceLaw :
      (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        lawRead := by
    exact ⟨hsame_refl lawRead, lawRoute⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        (fun row : BHist => hsame row lawRead ∧ Cont f g fg)
        (fun row : BHist => hsame row lawRead ∧ PkgSig bundle lawRead pkg)
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
        exact ⟨source.left, comp⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, lawPkg⟩
    }
  exact
    ⟨compositionData.left, comp, compositionData.right.left,
      compositionData.right.right.left, compositionData.right.right.right, cert⟩

end BEDC.Derived.KernelCategoryUp
