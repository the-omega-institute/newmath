import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_endpoint_seal_scope [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N radiusRead endpointRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont R S radiusRead ->
        Cont radiusRead E endpointRead ->
          Cont endpointRead C sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory C ∧
                UnaryHistory radiusRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory sealRead ∧ Cont R S radiusRead ∧
                    Cont radiusRead E endpointRead ∧ Cont endpointRead C sealRead ∧
                      Cont R S M ∧ Cont M E C ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier radiusRoute endpointRoute sealRoute sealPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, RUnary, _WUnary, SUnary, MUnary, EUnary,
    _HUnary, CUnary, _PUnary, _NUnary, _coefficientWindow, radiusMajorant,
    majorantEndpoint, carrierPkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed RUnary SUnary radiusRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed radiusUnary EUnary endpointRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary CUnary sealRoute
  exact
    ⟨RUnary, SUnary, EUnary, CUnary, radiusUnary, endpointUnary, sealUnary,
      radiusRoute, endpointRoute, sealRoute, radiusMajorant, majorantEndpoint, carrierPkg,
      sealPkg⟩

end BEDC.Derived.RealPowerSeriesUp
