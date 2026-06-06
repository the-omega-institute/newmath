import BEDC.Derived.RegSeqRatUp.CommonTailWindow

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatCommonTailTerminalSupportCarrierInversion [AskSetup] [PackageSetup]
    {source tail0 tail1 commonWindow endpoint radius regularity classifier0 classifier1
      classifierCommon realSeal transport route provenance cert terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatCommonTailWindowPacket source tail0 tail1 commonWindow endpoint radius regularity
        classifier0 classifier1 classifierCommon realSeal transport route provenance cert
        bundle pkg ->
      Cont route cert terminalRead ->
        PkgSig bundle terminalRead pkg ->
          UnaryHistory source ∧ UnaryHistory commonWindow ∧ UnaryHistory endpoint ∧
            UnaryHistory radius ∧ UnaryHistory regularity ∧ UnaryHistory realSeal ∧
              UnaryHistory terminalRead ∧ hsame classifier0 classifierCommon ∧
                hsame classifier1 classifierCommon ∧ Cont commonWindow realSeal transport ∧
                  Cont classifierCommon realSeal route ∧ Cont route cert terminalRead ∧
                    PkgSig bundle cert pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet terminalRoute terminalPkg
  obtain ⟨carrier0, _carrier1, _classifierFrom0, _classifierFrom1, commonWindowUnary,
    realSealUnary, _transportUnary, routeUnary, certUnary, sameClassifier0,
    sameClassifier1, commonWindowTransport, classifierSealRoute, certPkg⟩ := packet
  obtain ⟨sourceUnary, _tail0Unary, endpointUnary, radiusUnary, regularityUnary,
    _provenanceUnary, _classifier0Unary, _sourceTailEndpoint, _endpointRadiusRegularity,
    _regularityProvenanceClassifier0, _classifier0Pkg⟩ := carrier0
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary certUnary terminalRoute
  exact
    ⟨sourceUnary, commonWindowUnary, endpointUnary, radiusUnary, regularityUnary,
      realSealUnary, terminalReadUnary, sameClassifier0, sameClassifier1,
      commonWindowTransport, classifierSealRoute, terminalRoute, certPkg, terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
