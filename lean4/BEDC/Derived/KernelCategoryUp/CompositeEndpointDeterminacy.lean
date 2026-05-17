import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_composite_endpoint_determinacy
    [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name a b c f g composite :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      CategoryHomCarrier a b f ->
        CategoryHomCarrier b c g ->
          Cont f g composite ->
            PkgSig bundle composite pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row composite ∧ CategoryHomCarrier a c row)
                  (fun row : BHist => hsame row composite ∧ Cont f g row)
                  (fun row : BHist => hsame row composite ∧ PkgSig bundle composite pkg)
                  hsame ∧
                CategoryHomCarrier a c composite := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert CategoryHomCarrier
  intro _carrier left right comp pkgSig
  have compositeCarrier : CategoryHomCarrier a c composite :=
    CategoryHomCarrier_comp_closed left right comp
  have sourceComposite :
      (fun row : BHist => hsame row composite ∧ CategoryHomCarrier a c row) composite := by
    exact ⟨hsame_refl composite, compositeCarrier⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row composite ∧ CategoryHomCarrier a c row)
          (fun row : BHist => hsame row composite ∧ Cont f g row)
          (fun row : BHist => hsame row composite ∧ PkgSig bundle composite pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro composite sourceComposite
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              CategoryHomCarrier_hsame_transport
                (hsame_refl a) (hsame_refl c) sameRows source.right⟩
      }
      pattern_sound := by
        intro row source
        cases source.left
        exact ⟨hsame_refl composite, comp⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, compositeCarrier⟩

end BEDC.Derived.KernelCategoryUp
