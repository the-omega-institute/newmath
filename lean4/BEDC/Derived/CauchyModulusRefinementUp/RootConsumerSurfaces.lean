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

theorem CauchyModulusRefinementCarrier_terminal_pullback_consumer_uniqueness
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n terminalA terminalB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c terminalA ->
        Cont h c terminalB ->
          PkgSig bundle terminalA pkg ->
            PkgSig bundle terminalB pkg ->
              hsame terminalA terminalB ->
                SemanticNameCert
                  (fun row : BHist => hsame row terminalA ∧ UnaryHistory row)
                  (fun row : BHist => Cont h c row ∧ PkgSig bundle terminalA pkg)
                  (fun row : BHist => hsame row terminalB ∧ PkgSig bundle terminalB pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier terminalARoute terminalBRoute terminalAPkg terminalBPkg sameTerminal
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  have terminalAUnary : UnaryHistory terminalA :=
    unary_cont_closed hUnary cUnary terminalARoute
  have sourceTerminal :
      (fun row : BHist => hsame row terminalA ∧ UnaryHistory row) terminalA := by
    exact ⟨hsame_refl terminalA, terminalAUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro terminalA sourceTerminal
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact
        And.intro
          (cont_result_hsame_transport terminalARoute (hsame_symm source.left))
          terminalAPkg
    ledger_sound := by
      intro _row source
      exact And.intro (hsame_trans source.left sameTerminal) terminalBPkg
  }

end BEDC.Derived.CauchyModulusRefinementUp
