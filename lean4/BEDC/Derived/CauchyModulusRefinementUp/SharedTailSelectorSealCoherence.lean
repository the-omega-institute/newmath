import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_shared_tail_selector_seal_coherence
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q sealEndpoint ->
          PkgSig bundle sealEndpoint pkg ->
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory selected ∧
              UnaryHistory sealEndpoint ∧ Cont t w selected ∧
                Cont selected q sealEndpoint ∧ Cont q e h ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle sealEndpoint pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier selectedRoute sealEndpointRoute sealEndpointPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed selectedUnary qUnary sealEndpointRoute
  exact
    ⟨tUnary, wUnary, qUnary, selectedUnary, sealEndpointUnary, selectedRoute,
      sealEndpointRoute, qeh, pPkg, sealEndpointPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
