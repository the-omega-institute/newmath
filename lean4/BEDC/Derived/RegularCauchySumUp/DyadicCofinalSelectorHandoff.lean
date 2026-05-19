import BEDC.Derived.CauchyLimitSealUp
import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_dyadic_cofinal_selector_handoff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert leftWitness rightWitness sharedThreshold
      sharedRead : BHist}
    {sealSource sealSchedule sealDyadic sealDiagonal sealRow sealTransport sealProvenance
      sealLocalCert sealEndpoint sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      BEDC.Derived.CauchyLimitSealUp.CauchyLimitSealCarrier sealSource sealSchedule
          sealDyadic sealDiagonal sealRow sealTransport sealProvenance sealLocalCert
          sealEndpoint bundle pkg ->
        Cont leftSource leftWindow leftWitness ->
          Cont rightSource rightWindow rightWitness ->
            Cont leftWitness rightWitness sharedThreshold ->
              Cont sharedThreshold readback sharedRead ->
                Cont readback sealEndpoint sealRead ->
                  PkgSig bundle sharedRead pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory leftWitness ∧ UnaryHistory rightWitness ∧
                        UnaryHistory sharedThreshold ∧ UnaryHistory sharedRead ∧
                          UnaryHistory readback ∧ UnaryHistory sealEndpoint ∧
                            UnaryHistory sealRead ∧ Cont leftSource leftWindow leftWitness ∧
                              Cont rightSource rightWindow rightWitness ∧
                                Cont leftWitness rightWitness sharedThreshold ∧
                                  Cont sharedThreshold readback sharedRead ∧
                                    Cont sumEndpoint budget readback ∧
                                      Cont readback sealEndpoint sealRead ∧
                                        hsame sealEndpoint
                                          (append sealProvenance sealLocalCert) ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle sealEndpoint pkg ∧
                                              PkgSig bundle sharedRead pkg ∧
                                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro sumCarrier sealCarrier leftWitnessRoute rightWitnessRoute sharedThresholdRoute
    sharedReadRoute sealReadRoute sharedReadPkg sealReadPkg
  obtain ⟨leftSourceUnary, rightSourceUnary, leftWindowUnary, rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, provenancePkg⟩ := sumCarrier
  obtain ⟨_sealSourceUnary, _sealScheduleUnary, _sealDyadicUnary, _sealDiagonalUnary,
    _sealRowUnary, _sealTransportUnary, _sealProvenanceUnary, _sealLocalCertUnary,
    sealEndpointUnary, _sealSourceScheduleDyadic, _sealDyadicDiagonalSeal,
    _sealTransportProvenance, _sealProvenanceLocalEndpoint, sameSealEndpoint,
    sealEndpointPkg⟩ := sealCarrier
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
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed sharedThresholdUnary readbackUnary sharedReadRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sealEndpointUnary sealReadRoute
  exact
    ⟨leftWitnessUnary, rightWitnessUnary, sharedThresholdUnary, sharedReadUnary,
      readbackUnary, sealEndpointUnary, sealReadUnary, leftWitnessRoute, rightWitnessRoute,
      sharedThresholdRoute, sharedReadRoute, readbackRoute, sealReadRoute, sameSealEndpoint,
      provenancePkg, sealEndpointPkg, sharedReadPkg, sealReadPkg⟩

end BEDC.Derived.RegularCauchySumUp
