import BEDC.Derived.RegSeqRatUp.CommonTailWindow

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatAuditThresholdFiniteCoverGluing [AskSetup] [PackageSetup]
    {source tail0 tail1 commonWindow endpoint radius regularity classifier0 classifier1
      classifierCommon realSeal transport route provenance cert terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatCommonTailWindowPacket source tail0 tail1 commonWindow endpoint radius
        regularity classifier0 classifier1 classifierCommon realSeal transport route
        provenance cert bundle pkg →
      Cont route cert terminalRead →
        PkgSig bundle terminalRead pkg →
          UnaryHistory commonWindow ∧ UnaryHistory classifierCommon ∧
            UnaryHistory realSeal ∧ UnaryHistory terminalRead ∧
              hsame classifier0 classifierCommon ∧ hsame classifier1 classifierCommon ∧
                Cont commonWindow realSeal transport ∧
                  Cont classifierCommon realSeal route ∧ Cont route cert terminalRead ∧
                    PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routeCertTerminal terminalPkg
  obtain ⟨_carrier0, _carrier1, classifierFrom0, _classifierFrom1,
    commonWindowUnary, realSealUnary, _transportUnary, routeUnary, certUnary,
    sameClassifier0, sameClassifier1, commonWindowTransport, classifierSealRoute,
    _certPkg⟩ := packet
  obtain ⟨_endpointUnary, _radiusUnary, _regularityUnary, _classifier0Unary,
    _endpointUnaryCommon, _radiusUnaryCommon, _regularityUnaryCommon,
    classifierCommonUnary, _sameEndpoint, _sameRadius, _sameRegularity,
    _sameReadback⟩ := classifierFrom0
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary certUnary routeCertTerminal
  exact
    ⟨commonWindowUnary, classifierCommonUnary, realSealUnary, terminalUnary,
      sameClassifier0, sameClassifier1, commonWindowTransport, classifierSealRoute,
      routeCertTerminal, terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
