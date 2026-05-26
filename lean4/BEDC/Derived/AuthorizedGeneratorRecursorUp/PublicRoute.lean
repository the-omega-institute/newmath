import BEDC.Derived.AuthorizedGeneratorRecursorUp.DisplayedRouteSurface

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPublicRoute [AskSetup] [PackageSetup]
    {authorization generator fuel route provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorDisplayedRoute authorization generator fuel route provenance name
        bundle pkg →
      Cont fuel route publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row authorization ∨ hsame row generator ∨ hsame row fuel ∨
                  hsame row route ∨ hsame row publicRead)
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead ∧ Cont fuel route publicRead ∧
              PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro displayed fuelRoute publicPkg
  obtain ⟨_authorizationUnary, _generatorUnary, fuelUnary, routeUnary, _provenanceUnary,
    _nameUnary, _authorizationGeneratorRoute, _provenancePkg, _namePkg⟩ := displayed
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed fuelUnary routeUnary fuelRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row authorization ∨ hsame row generator ∨ hsame row fuel ∨
            hsame row route ∨ hsame row publicRead)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }
  exact ⟨cert, publicUnary, fuelRoute, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
