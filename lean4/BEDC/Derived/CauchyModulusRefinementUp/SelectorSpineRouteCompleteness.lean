import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_spine_route_completeness
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead selectorEndpoint
      l10Endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              Cont publicRead c selectorEndpoint ->
                Cont selectorEndpoint n l10Endpoint ->
                  PkgSig bundle l10Endpoint pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                            bundle pkg ∧
                          hsame row l10Endpoint)
                      (fun row : BHist =>
                        Cont u v t ∧ Cont t w selected ∧ Cont selected q readback ∧
                          Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                            Cont publicRead c selectorEndpoint ∧
                              Cont selectorEndpoint n row ∧
                                PkgSig bundle l10Endpoint pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle l10Endpoint pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicCSelector
    selectorNL10 l10Pkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  have selectorEndpointUnary : UnaryHistory selectorEndpoint :=
    unary_cont_closed publicReadUnary cUnary publicCSelector
  have l10Unary : UnaryHistory l10Endpoint :=
    unary_cont_closed selectorEndpointUnary nUnary selectorNL10
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro l10Endpoint (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl l10Endpoint))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨uvt, tWSelected, selectedQReadback, readbackESeal, sealHPublic, publicCSelector,
          cont_result_hsame_transport selectorNL10 (hsame_symm source.right), l10Pkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport l10Unary (hsame_symm source.right), l10Pkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
