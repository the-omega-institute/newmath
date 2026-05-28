import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_obligation_radius_export [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coefficientRead radiusRead obligationRead
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coefficientRead ->
        Cont R S radiusRead ->
          Cont S M obligationRead ->
            Cont obligationRead E endpointRead ->
              PkgSig bundle endpointRead pkg ->
                UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧
                  UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory coefficientRead ∧
                    UnaryHistory radiusRead ∧ UnaryHistory obligationRead ∧
                      UnaryHistory endpointRead ∧ Cont A W coefficientRead ∧
                        Cont R S radiusRead ∧ Cont S M obligationRead ∧
                          Cont obligationRead E endpointRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: RealPowerSeriesCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coefficientRoute radiusRoute obligationRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed AUnary WUnary coefficientRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed RUnary SUnary radiusRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed SUnary MUnary obligationRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed obligationUnary EUnary endpointRoute
  exact
    ⟨AUnary, RUnary, WUnary, SUnary, MUnary, EUnary, coefficientUnary, radiusUnary,
      obligationUnary, endpointUnary, coefficientRoute, radiusRoute, obligationRoute,
      endpointRoute, pkgSig, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
