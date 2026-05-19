import BEDC.Derived.CauchyLimitFunctorUp

namespace BEDC.Derived.CauchyLimitFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitFunctorUp_StdBridge [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint terminalRead bridgeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg ->
      Cont targetSeal endpoint terminalRead ->
        Cont terminalRead routes bridgeRead ->
          PkgSig bundle bridgeRead pkg ->
            UnaryHistory sourceSeal /\ UnaryHistory targetSeal /\ UnaryHistory transportMap /\
              UnaryHistory sourceWindow /\ UnaryHistory targetWindow /\ UnaryHistory readback /\
                UnaryHistory tolerance /\ UnaryHistory classifier /\ UnaryHistory endpoint /\
                  UnaryHistory terminalRead /\ UnaryHistory bridgeRead /\
                    Cont sourceSeal transportMap targetSeal /\
                      Cont sourceWindow targetWindow readback /\
                        Cont readback tolerance classifier /\
                          Cont classifier endpoint carrierEndpoint /\
                            Cont targetSeal endpoint terminalRead /\
                              Cont terminalRead routes bridgeRead /\
                                PkgSig bundle carrierEndpoint pkg /\
                                  PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier targetEndpointTerminal terminalRoutesBridge bridgePkg
  obtain ⟨sourceSealUnary, targetSealUnary, transportMapUnary, sourceWindowUnary,
    targetWindowUnary, readbackUnary, toleranceUnary, classifierUnary, endpointUnary,
    _hsameRowsUnary, routesUnary, _provenanceUnary, _nameCertUnary, _carrierEndpointUnary,
    sourceTransportTarget, sourceTargetReadback, readbackToleranceClassifier,
    classifierEndpointCarrier, _hsameRowsRoutesProvenance, carrierEndpointPkg⟩ := carrier
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed targetSealUnary endpointUnary targetEndpointTerminal
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed terminalReadUnary routesUnary terminalRoutesBridge
  exact
    ⟨sourceSealUnary, targetSealUnary, transportMapUnary, sourceWindowUnary,
      targetWindowUnary, readbackUnary, toleranceUnary, classifierUnary, endpointUnary,
      terminalReadUnary, bridgeReadUnary, sourceTransportTarget, sourceTargetReadback,
      readbackToleranceClassifier, classifierEndpointCarrier, targetEndpointTerminal,
      terminalRoutesBridge, carrierEndpointPkg, bridgePkg⟩

end BEDC.Derived.CauchyLimitFunctorUp
