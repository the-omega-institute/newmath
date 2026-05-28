import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_evaluation_window_exhaustion [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N evalRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W evalRead ->
        Cont evalRead S endpointRead ->
          PkgSig bundle endpointRead pkg ->
            UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory evalRead ∧
              UnaryHistory endpointRead ∧ Cont A W evalRead ∧
                Cont evalRead S endpointRead ∧ Cont R S M ∧ Cont M E C ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier evalRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  have evalUnary : UnaryHistory evalRead :=
    unary_cont_closed AUnary WUnary evalRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed evalUnary SUnary endpointRoute
  exact
    ⟨AUnary, WUnary, SUnary, evalUnary, endpointUnary, evalRoute, endpointRoute,
      radiusMajorant, majorantEndpoint, pkgSig, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
