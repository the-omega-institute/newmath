import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_shared_tail_meet_handoff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert leftWitness rightWitness sharedThreshold
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg →
      Cont leftSource leftWindow leftWitness →
        Cont rightSource rightWindow rightWitness →
          Cont leftWitness rightWitness sharedThreshold →
            Cont sharedThreshold readback realRead →
              PkgSig bundle realRead pkg →
                UnaryHistory leftWitness ∧ UnaryHistory rightWitness ∧
                  UnaryHistory sharedThreshold ∧ UnaryHistory realRead ∧
                    Cont leftSource leftWindow leftWitness ∧
                      Cont rightSource rightWindow rightWitness ∧
                        Cont leftWitness rightWitness sharedThreshold ∧
                          Cont sharedThreshold readback realRead ∧
                            Cont leftEndpoint rightEndpoint sumEndpoint ∧
                              Cont sumEndpoint budget readback ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier leftWitnessRoute rightWitnessRoute sharedThresholdRoute realReadRoute
    realReadPkg
  obtain ⟨leftSourceUnary, rightSourceUnary, leftWindowUnary, rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, provenancePkg⟩ := carrier
  have leftWitnessUnary : UnaryHistory leftWitness :=
    unary_cont_closed leftSourceUnary leftWindowUnary leftWitnessRoute
  have rightWitnessUnary : UnaryHistory rightWitness :=
    unary_cont_closed rightSourceUnary rightWindowUnary rightWitnessRoute
  have sharedThresholdUnary : UnaryHistory sharedThreshold :=
    unary_cont_closed leftWitnessUnary rightWitnessUnary sharedThresholdRoute
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sharedThresholdUnary readbackUnary realReadRoute
  exact
    ⟨leftWitnessUnary,
      rightWitnessUnary,
      sharedThresholdUnary,
      realReadUnary,
      leftWitnessRoute,
      rightWitnessRoute,
      sharedThresholdRoute,
      realReadRoute,
      sumEndpointRoute,
      readbackRoute,
      provenancePkg,
      realReadPkg⟩

end BEDC.Derived.RegularCauchySumUp
