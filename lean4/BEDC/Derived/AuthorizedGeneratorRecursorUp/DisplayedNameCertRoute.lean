import BEDC.Derived.AuthorizedGeneratorRecursorUp.DisplayedRouteSurface

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorNameCertRoute [AskSetup] [PackageSetup]
    {authorization generator fuel route provenance name branchRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorDisplayedRoute authorization generator fuel route provenance name
        bundle pkg →
      Cont authorization generator branchRead →
        Cont fuel route outputRead →
          PkgSig bundle outputRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                AuthorizedGeneratorRecursorDisplayedRoute authorization generator fuel route
                    provenance name bundle pkg ∧ hsame row outputRead)
              (fun row : BHist =>
                Cont authorization generator branchRead ∧ Cont fuel route row ∧
                  UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle outputRead pkg ∧
                  hsame row outputRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro displayed authorizationGeneratorBranch fuelRouteOutput outputPkg
  have displayedPacket :
      AuthorizedGeneratorRecursorDisplayedRoute authorization generator fuel route provenance name
        bundle pkg :=
    displayed
  obtain ⟨_authorizationUnary, _generatorUnary, fuelUnary, routeUnary, _provenanceUnary,
    _nameUnary, _authorizationGeneratorRoute, provenancePkg, _namePkg⟩ := displayed
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed fuelUnary routeUnary fuelRouteOutput
  exact {
    core := {
      carrier_inhabited := Exists.intro outputRead
        (And.intro displayedPacket (hsame_refl outputRead))
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
          ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨authorizationGeneratorBranch,
          cont_result_hsame_transport fuelRouteOutput (hsame_symm source.right),
          unary_transport outputUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, outputPkg, source.right⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
