import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_product_coefficient_window_lock [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N productRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W productRead ->
        Cont productRead S endpointRead ->
          PkgSig bundle endpointRead pkg ->
            UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧
              UnaryHistory productRead ∧ UnaryHistory endpointRead ∧
                Cont A W productRead ∧ Cont productRead S endpointRead ∧
                  Cont R S M ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier productRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed AUnary WUnary productRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed productReadUnary SUnary endpointRoute
  exact
    ⟨AUnary, WUnary, SUnary, MUnary, productReadUnary, endpointReadUnary,
      productRoute, endpointRoute, radiusMajorant, carrierPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
