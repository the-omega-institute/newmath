import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_tail_selector_compatibility [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert leftPrecision leftStream leftRegularity
      leftDyadic leftRealSeal leftWitness leftTransports leftRoutes leftProvenance
      leftLocalCert rightPrecision rightStream rightRegularity rightDyadic rightRealSeal
      rightWitness rightTransports rightRoutes rightProvenance rightLocalCert leftConsumer
      rightConsumer sumConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      BEDC.Derived.RegularCauchyTailSelectorUp.RegularCauchyTailSelectorCarrier leftPrecision
          leftStream leftRegularity leftDyadic leftRealSeal leftWitness leftTransports leftRoutes
          leftProvenance leftLocalCert bundle pkg ->
        BEDC.Derived.RegularCauchyTailSelectorUp.RegularCauchyTailSelectorCarrier rightPrecision
            rightStream rightRegularity rightDyadic rightRealSeal rightWitness rightTransports
            rightRoutes rightProvenance rightLocalCert bundle pkg ->
          Cont leftWitness leftRoutes leftConsumer ->
            Cont rightWitness rightRoutes rightConsumer ->
              Cont readback routes sumConsumer ->
                PkgSig bundle sumConsumer pkg ->
                  UnaryHistory leftWitness ∧ UnaryHistory rightWitness ∧ UnaryHistory readback ∧
                    UnaryHistory leftConsumer ∧ UnaryHistory rightConsumer ∧
                      UnaryHistory sumConsumer ∧ Cont leftRegularity leftDyadic leftWitness ∧
                        Cont rightRegularity rightDyadic rightWitness ∧
                          Cont readback routes sumConsumer ∧ PkgSig bundle leftProvenance pkg ∧
                            PkgSig bundle rightProvenance pkg ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle sumConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro sumCarrier leftCarrier rightCarrier leftWitnessConsumer rightWitnessConsumer
    readbackRoutesSumConsumer sumConsumerPkg
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, provenancePkg⟩ := sumCarrier
  obtain ⟨_leftPrecisionUnary, _leftStreamUnary, leftRegularityUnary, leftDyadicUnary,
    _leftRealSealUnary, _leftTransportsUnary, leftRoutesUnary, _leftProvenanceUnary,
    _leftLocalCertUnary, leftWitnessRoute, _leftProvenanceRoute, _leftLocalCertRoute,
    leftProvenancePkg⟩ := leftCarrier
  obtain ⟨_rightPrecisionUnary, _rightStreamUnary, rightRegularityUnary, rightDyadicUnary,
    _rightRealSealUnary, _rightTransportsUnary, rightRoutesUnary, _rightProvenanceUnary,
    _rightLocalCertUnary, rightWitnessRoute, _rightProvenanceRoute, _rightLocalCertRoute,
    rightProvenancePkg⟩ := rightCarrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have leftWitnessUnary : UnaryHistory leftWitness :=
    unary_cont_closed leftRegularityUnary leftDyadicUnary leftWitnessRoute
  have rightWitnessUnary : UnaryHistory rightWitness :=
    unary_cont_closed rightRegularityUnary rightDyadicUnary rightWitnessRoute
  have leftConsumerUnary : UnaryHistory leftConsumer :=
    unary_cont_closed leftWitnessUnary leftRoutesUnary leftWitnessConsumer
  have rightConsumerUnary : UnaryHistory rightConsumer :=
    unary_cont_closed rightWitnessUnary rightRoutesUnary rightWitnessConsumer
  have sumConsumerUnary : UnaryHistory sumConsumer :=
    unary_cont_closed readbackUnary routesUnary readbackRoutesSumConsumer
  exact
    ⟨leftWitnessUnary,
      rightWitnessUnary,
      readbackUnary,
      leftConsumerUnary,
      rightConsumerUnary,
      sumConsumerUnary,
      leftWitnessRoute,
      rightWitnessRoute,
      readbackRoutesSumConsumer,
      leftProvenancePkg,
      rightProvenancePkg,
      provenancePkg,
      sumConsumerPkg⟩

end BEDC.Derived.RegularCauchySumUp
