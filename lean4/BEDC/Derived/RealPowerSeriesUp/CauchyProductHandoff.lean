import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_cauchy_product_handoff [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N productWindow productRead regRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W productWindow ->
        Cont productWindow S productRead ->
          Cont productRead M regRead ->
            Cont regRead E endpointRead ->
              PkgSig bundle endpointRead pkg ->
                UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧
                  UnaryHistory E ∧ UnaryHistory productWindow ∧ UnaryHistory productRead ∧
                    UnaryHistory regRead ∧ UnaryHistory endpointRead ∧
                      Cont A W productWindow ∧ Cont productWindow S productRead ∧
                        Cont productRead M regRead ∧ Cont regRead E endpointRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier productWindowRoute productReadRoute regReadRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have productWindowUnary : UnaryHistory productWindow :=
    unary_cont_closed AUnary WUnary productWindowRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed productWindowUnary SUnary productReadRoute
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed productReadUnary MUnary regReadRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed regReadUnary EUnary endpointRoute
  exact
    ⟨AUnary, WUnary, SUnary, MUnary, EUnary, productWindowUnary, productReadUnary,
      regReadUnary, endpointReadUnary, productWindowRoute, productReadRoute, regReadRoute,
      endpointRoute, carrierPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
