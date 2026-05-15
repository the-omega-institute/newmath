import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_window_front_totality
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootFront selected readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u rootFront ->
        Cont t w selected ->
          Cont selected q readback ->
            Cont readback e sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory rootFront /\ UnaryHistory selected /\ UnaryHistory readback /\
                  UnaryHistory sealRead /\ Cont m0 m1 u /\ Cont m0 u rootFront /\
                    Cont u v t /\ Cont t w selected /\ Cont selected q readback /\
                      Cont readback e sealRead /\ PkgSig bundle p pkg /\
                        PkgSig bundle sealRead pkg /\ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier m0URootFront tWSelected selectedQReadback readbackESealRead sealReadPkg
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have rootFrontUnary : UnaryHistory rootFront :=
    unary_cont_closed m0Unary uUnary m0URootFront
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESealRead
  exact
    ⟨rootFrontUnary, selectedUnary, readbackUnary, sealReadUnary, m0m1u, m0URootFront,
      uvt, tWSelected, selectedQReadback, readbackESealRead, pPkg, sealReadPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
