import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_namecert_root_route_readiness [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      Cont identity composition hom →
        Cont hom name rootRead →
          PkgSig bundle rootRead pkg →
            UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
              Cont identity composition hom ∧ Cont hom name rootRead ∧
                hsame associativity (append hom composition) ∧ hsame unit identity ∧
                  hsame name (append provenance unit) ∧ PkgSig bundle rootRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row rootRead ∧ Cont hom name rootRead)
                      (fun row : BHist =>
                        hsame row identity ∨ hsame row hom ∨ hsame row rootRead)
                      (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig CategoryHomCarrier
  intro carrier identityComposition rootRoute rootPkg
  obtain ⟨unaryObject, identityCarrier, _carrierComposition, associativitySame, unitSame,
    nameSame⟩ := carrier
  have sourceRoot :
      (fun row : BHist => hsame row rootRead ∧ Cont hom name rootRead) rootRead := by
    exact ⟨hsame_refl rootRead, rootRoute⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ Cont hom name rootRead)
        (fun row : BHist => hsame row identity ∨ hsame row hom ∨ hsame row rootRead)
        (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootRead sourceRoot
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, rootPkg⟩
    }
  exact
    ⟨unaryObject, identityCarrier, identityComposition, rootRoute, associativitySame,
      unitSame, nameSame, rootPkg, cert⟩

end BEDC.Derived.KernelCategoryUp
