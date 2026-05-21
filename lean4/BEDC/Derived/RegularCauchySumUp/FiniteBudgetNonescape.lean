import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_finite_budget_nonescape [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert budgetRead routeRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont budget readback budgetRead ->
        Cont readback routes routeRead ->
          Cont routeRead localCert finalRead ->
            PkgSig bundle finalRead pkg ->
              UnaryHistory budget ∧ UnaryHistory readback ∧ UnaryHistory budgetRead ∧
                UnaryHistory routeRead ∧ UnaryHistory finalRead ∧
                  Cont sumEndpoint budget readback ∧ Cont budget readback budgetRead ∧
                    Cont readback routes routeRead ∧ Cont routeRead localCert finalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier budgetRoute routeRoute finalRoute finalPkg
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, routesUnary,
    _provenanceUnary, localCertUnary, _leftRoute, _rightRoute, sumRoute, readbackRoute,
    _provenanceRoute, provenancePkg⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetUnary readbackUnary budgetRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed readbackUnary routesUnary routeRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed routeReadUnary localCertUnary finalRoute
  exact
    ⟨budgetUnary,
      readbackUnary,
      budgetReadUnary,
      routeReadUnary,
      finalReadUnary,
      readbackRoute,
      budgetRoute,
      routeRoute,
      finalRoute,
      provenancePkg,
      finalPkg⟩

end BEDC.Derived.RegularCauchySumUp
