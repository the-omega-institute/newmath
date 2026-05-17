import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_route_determinacy [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          Cont readback e sealRow →
            Cont sealRow h endpoint →
              PkgSig bundle endpoint pkg →
                UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                  UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                    UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                      UnaryHistory endpoint ∧ Cont m0 m1 u ∧ Cont u v t ∧
                        Cont t w selected ∧ Cont selected q readback ∧
                          Cont readback e sealRow ∧ Cont sealRow h endpoint ∧
                            PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg ∧
                              hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier selectedRoute readbackRoute sealRoute endpointRoute endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary hUnary endpointRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, selectedUnary,
      readbackUnary, sealUnary, endpointUnary, m0m1u, uvt, selectedRoute, readbackRoute,
      sealRoute, endpointRoute, pPkg, endpointPkg, hn⟩

theorem CauchyModulusRefinementCarrier_l10_row_exactness [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n b s d r selectorSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      UnaryHistory b -> UnaryHistory s -> UnaryHistory d ->
        Cont b s w -> Cont w d r -> Cont r e selectorSeal ->
          PkgSig bundle selectorSeal pkg ->
            UnaryHistory r ∧ UnaryHistory selectorSeal ∧ Cont b s w ∧ Cont w d r ∧
              Cont r e selectorSeal ∧ Cont t w q ∧ Cont q e h ∧ PkgSig bundle p pkg ∧
                PkgSig bundle selectorSeal pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier bUnary sUnary dUnary bsw wdr selectorRoute selectorPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, wUnary, _qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, twq, qeh, pPkg, hn⟩
  have rUnary : UnaryHistory r :=
    unary_cont_closed wUnary dUnary wdr
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed rUnary eUnary selectorRoute
  exact ⟨rUnary, selectorSealUnary, bsw, wdr, selectorRoute, twq, qeh, pPkg,
    selectorPkg, hn⟩

theorem CauchyModulusRefinementCarrier_real_window_budget_pullback [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n request dyadic regular disclosure terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w request -> Cont request q dyadic -> Cont dyadic e regular ->
        Cont regular h disclosure -> Cont disclosure c terminal ->
          PkgSig bundle terminal pkg ->
            UnaryHistory request ∧ UnaryHistory dyadic ∧ UnaryHistory regular ∧
              UnaryHistory disclosure ∧ UnaryHistory terminal ∧ Cont t w request ∧
                Cont request q dyadic ∧ Cont dyadic e regular ∧ Cont regular h disclosure ∧
                  Cont disclosure c terminal ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle terminal pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier requestRoute dyadicRoute regularRoute disclosureRoute terminalRoute terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have requestUnary : UnaryHistory request :=
    unary_cont_closed tUnary wUnary requestRoute
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed requestUnary qUnary dyadicRoute
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed dyadicUnary eUnary regularRoute
  have disclosureUnary : UnaryHistory disclosure :=
    unary_cont_closed regularUnary hUnary disclosureRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed disclosureUnary cUnary terminalRoute
  exact
    ⟨requestUnary, dyadicUnary, regularUnary, disclosureUnary, terminalUnary, requestRoute,
      dyadicRoute, regularRoute, disclosureRoute, terminalRoute, pPkg, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
