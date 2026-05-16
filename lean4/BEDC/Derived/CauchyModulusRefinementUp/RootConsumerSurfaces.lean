import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_window_route_factorization [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              Cont h c endpoint ->
                PkgSig bundle publicRead pkg ->
                  PkgSig bundle endpoint pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                          bundle pkg ∧ hsame row endpoint)
                      (fun row : BHist =>
                        Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                          Cont selected q readback ∧ Cont readback e sealRead ∧
                            Cont sealRead h publicRead ∧ Cont h c row ∧
                              PkgSig bundle publicRead pkg ∧ PkgSig bundle endpoint pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier selectedRoute readbackRoute sealRoute publicRoute endpointRoute publicPkg
    endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierFull :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary endpointRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrierFull (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨m0m1u, uvt, selectedRoute, readbackRoute, sealRoute, publicRoute,
          cont_result_hsame_transport endpointRoute (hsame_symm source.right), publicPkg,
          endpointPkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport endpointUnary (hsame_symm source.right)) endpointPkg
  }

end BEDC.Derived.CauchyModulusRefinementUp
