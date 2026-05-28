import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_coefficient_tail_obligations [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N tail productRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W tail ->
        Cont tail S productRead ->
          Cont productRead E endpointRead ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory E ∧
                UnaryHistory tail ∧ UnaryHistory productRead ∧ UnaryHistory endpointRead ∧
                  Cont A W tail ∧ Cont tail S productRead ∧
                    Cont productRead E endpointRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier coefficientTail tailProductRead productEndpointRead endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed AUnary WUnary coefficientTail
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed tailUnary SUnary tailProductRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed productReadUnary EUnary productEndpointRead
  exact
    ⟨AUnary, WUnary, SUnary, EUnary, tailUnary, productReadUnary, endpointReadUnary,
      coefficientTail, tailProductRead, productEndpointRead, pkgSig, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
