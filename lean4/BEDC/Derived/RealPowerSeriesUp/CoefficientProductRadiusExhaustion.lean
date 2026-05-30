import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_coefficient_product_radius_exhaustion [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N productLedger productRead radiusRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg →
      Cont A W productLedger →
        Cont productLedger S productRead →
          Cont R S radiusRead →
            Cont radiusRead E endpointRead →
              PkgSig bundle productRead pkg →
                PkgSig bundle endpointRead pkg →
                  UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory R ∧
                    UnaryHistory E ∧ UnaryHistory productLedger ∧
                      UnaryHistory productRead ∧ UnaryHistory radiusRead ∧
                        UnaryHistory endpointRead ∧ Cont A W productLedger ∧
                          Cont productLedger S productRead ∧ Cont R S radiusRead ∧
                            Cont radiusRead E endpointRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle productRead pkg ∧
                                PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier productLedgerRoute productReadRoute radiusRoute endpointRoute productPkg
    endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, _MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed AUnary WUnary productLedgerRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed productLedgerUnary SUnary productReadRoute
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed RUnary SUnary radiusRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed radiusReadUnary EUnary endpointRoute
  exact
    ⟨AUnary, WUnary, SUnary, RUnary, EUnary, productLedgerUnary, productReadUnary,
      radiusReadUnary, endpointReadUnary, productLedgerRoute, productReadRoute, radiusRoute,
      endpointRoute, carrierPkg, productPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
