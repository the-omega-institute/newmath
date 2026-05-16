import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_observation_budget_handoff
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n observationRequest observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w observationRequest ->
        Cont observationRequest q observationRead ->
          PkgSig bundle observationRead pkg ->
            UnaryHistory observationRequest ∧ UnaryHistory observationRead ∧
              Cont m0 m1 u ∧ Cont u v t ∧ Cont t w observationRequest ∧
                Cont observationRequest q observationRead ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle observationRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier requestRoute readRoute readPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have requestUnary : UnaryHistory observationRequest :=
    unary_cont_closed tUnary wUnary requestRoute
  have readUnary : UnaryHistory observationRead :=
    unary_cont_closed requestUnary qUnary readRoute
  exact
    ⟨requestUnary, readUnary, m0m1u, uvt, requestRoute, readRoute, pPkg, readPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
