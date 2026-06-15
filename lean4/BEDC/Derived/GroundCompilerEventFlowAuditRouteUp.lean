import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GroundCompilerEventFlowAuditRouteCarrier [AskSetup] [PackageSetup]
    (eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory eventFlow ∧ UnaryHistory legalChannel ∧ UnaryHistory lossless ∧
    UnaryHistory recognizer ∧ UnaryHistory certificateGate ∧ UnaryHistory nonEvidence ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont eventFlow legalChannel lossless ∧
          Cont lossless recognizer certificateGate ∧ Cont nonEvidence transport replay ∧
            Cont replay provenance localName ∧ PkgSig bundle localName pkg

theorem GroundCompilerEventFlowAuditRouteCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg ->
      UnaryHistory eventFlow ∧ UnaryHistory legalChannel ∧ UnaryHistory lossless ∧
        UnaryHistory recognizer ∧ UnaryHistory certificateGate ∧ UnaryHistory nonEvidence ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory localName ∧ Cont eventFlow legalChannel lossless ∧
              Cont lossless recognizer certificateGate ∧ Cont nonEvidence transport replay ∧
                Cont replay provenance localName ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨eventFlowUnary, legalChannelUnary, losslessUnary, recognizerUnary,
    certificateGateUnary, nonEvidenceUnary, transportUnary, replayUnary, provenanceUnary,
    localNameUnary, eventFlowLegalLossless, losslessRecognizerGate,
    nonEvidenceTransportReplay, replayProvenanceLocalName, localNamePkg⟩ := carrier
  exact
    ⟨eventFlowUnary, legalChannelUnary, losslessUnary, recognizerUnary, certificateGateUnary,
      nonEvidenceUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
      eventFlowLegalLossless, losslessRecognizerGate, nonEvidenceTransportReplay,
      replayProvenanceLocalName, localNamePkg⟩

end BEDC.Derived.GroundCompilerEventFlowAuditRouteUp
