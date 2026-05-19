import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_non_escape_boundary [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont readback routes consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory leftSource ∧ UnaryHistory rightSource ∧ UnaryHistory leftWindow ∧
            UnaryHistory rightWindow ∧ UnaryHistory leftEndpoint ∧ UnaryHistory rightEndpoint ∧
              UnaryHistory sumEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
                UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
                  UnaryHistory localCert ∧ UnaryHistory consumer ∧
                    Cont leftWindow leftEndpoint transports ∧
                      Cont rightWindow rightEndpoint routes ∧
                        Cont leftEndpoint rightEndpoint sumEndpoint ∧
                          Cont sumEndpoint budget readback ∧ Cont readback routes consumer ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨leftSourceUnary, rightSourceUnary, leftWindowUnary, rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, transportsUnary, routesUnary,
    provenanceUnary, localCertUnary, leftRoute, rightRoute, sumEndpointRoute, readbackRoute,
    _provenanceRoute, provenancePkg⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed readbackUnary routesUnary consumerRoute
  exact
    ⟨leftSourceUnary,
      rightSourceUnary,
      leftWindowUnary,
      rightWindowUnary,
      leftEndpointUnary,
      rightEndpointUnary,
      sumEndpointUnary,
      budgetUnary,
      readbackUnary,
      transportsUnary,
      routesUnary,
      provenanceUnary,
      localCertUnary,
      consumerUnary,
      leftRoute,
      rightRoute,
      sumEndpointRoute,
      readbackRoute,
      consumerRoute,
      provenancePkg,
      consumerPkg⟩

end BEDC.Derived.RegularCauchySumUp
