import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesRootEndpointNonescape [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N rootRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont R M rootRead ->
        Cont rootRead E endpointRead ->
          PkgSig bundle endpointRead pkg ->
            UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory rootRead ∧
              UnaryHistory endpointRead ∧ Cont R S M ∧ Cont R M rootRead ∧
                Cont rootRead E endpointRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier rootRoute endpointRoute endpointPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, RUnary, _WUnary, _SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientRoute, radiusRoute,
    _endpointCarrierRoute, carrierPkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed RUnary MUnary rootRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rootUnary EUnary endpointRoute
  exact
    ⟨RUnary, MUnary, EUnary, rootUnary, endpointUnary, radiusRoute, rootRoute,
      endpointRoute, carrierPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
