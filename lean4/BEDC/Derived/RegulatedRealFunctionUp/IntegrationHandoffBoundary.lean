import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatedRealFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedRealFunctionCarrier [AskSetup] [PackageSetup]
    (interval approxLedger tailLedger uniformRoute endpointSeal transportRow replayRow
      provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory interval ∧ UnaryHistory approxLedger ∧ UnaryHistory tailLedger ∧
    UnaryHistory uniformRoute ∧ UnaryHistory endpointSeal ∧ UnaryHistory transportRow ∧
      UnaryHistory replayRow ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont interval approxLedger tailLedger ∧ Cont tailLedger uniformRoute endpointSeal ∧
          Cont endpointSeal transportRow replayRow ∧ Cont replayRow provenance localCert ∧
            PkgSig bundle provenance pkg

theorem RegulatedRealFunctionCarrier_integration_facing_handoff_boundary [AskSetup]
    [PackageSetup]
    {interval approxLedger tailLedger uniformRoute endpointSeal transportRow replayRow
      provenance localCert integrationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedRealFunctionCarrier interval approxLedger tailLedger uniformRoute endpointSeal
        transportRow replayRow provenance localCert bundle pkg ->
      Cont endpointSeal replayRow integrationRead ->
        PkgSig bundle integrationRead pkg ->
          UnaryHistory interval ∧ UnaryHistory approxLedger ∧ UnaryHistory tailLedger ∧
            UnaryHistory uniformRoute ∧ UnaryHistory endpointSeal ∧
              UnaryHistory integrationRead ∧ Cont interval approxLedger tailLedger ∧
                Cont tailLedger uniformRoute endpointSeal ∧
                  Cont endpointSeal replayRow integrationRead ∧
                    PkgSig bundle provenance pkg ∧
                      PkgSig bundle integrationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier endpointReplayRead integrationPkg
  obtain ⟨intervalUnary, approxUnary, tailUnary, uniformUnary, endpointUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, intervalApproxTail,
    tailUniformEndpoint, _endpointTransportReplay, _replayProvenanceLocal,
    provenancePkg⟩ := carrier
  have integrationUnary : UnaryHistory integrationRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  exact
    ⟨intervalUnary, approxUnary, tailUnary, uniformUnary, endpointUnary, integrationUnary,
      intervalApproxTail, tailUniformEndpoint, endpointReplayRead, provenancePkg, integrationPkg⟩

end BEDC.Derived.RegulatedRealFunctionUp
