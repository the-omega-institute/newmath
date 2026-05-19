import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_budget_associative_visibility [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert reassocBudget visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont budget readback reassocBudget ->
        Cont reassocBudget routes visibleRead ->
          PkgSig bundle visibleRead pkg ->
            UnaryHistory sumEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
              UnaryHistory reassocBudget ∧ UnaryHistory visibleRead ∧
                Cont sumEndpoint budget readback ∧ Cont budget readback reassocBudget ∧
                  Cont reassocBudget routes visibleRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle visibleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier reassocRoute visibleRoute visiblePkg
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, provenancePkg⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have reassocUnary : UnaryHistory reassocBudget :=
    unary_cont_closed budgetUnary readbackUnary reassocRoute
  have visibleUnary : UnaryHistory visibleRead :=
    unary_cont_closed reassocUnary routesUnary visibleRoute
  exact
    ⟨sumEndpointUnary, budgetUnary, readbackUnary, reassocUnary, visibleUnary,
      readbackRoute, reassocRoute, visibleRoute, provenancePkg, visiblePkg⟩

end BEDC.Derived.RegularCauchySumUp
