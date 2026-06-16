import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem GroundCompilerEventFlowAuditRouteCarrier_channel_lossless_boundary
    [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row certificateGate ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eventFlow ∨ hsame row legalChannel ∨ hsame row lossless ∨
              hsame row recognizer ∨ hsame row certificateGate)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame ∧
        Cont eventFlow legalChannel lossless ∧ Cont lossless recognizer certificateGate ∧
          PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_eventFlowUnary, _legalChannelUnary, _losslessUnary, _recognizerUnary,
    certificateGateUnary, _nonEvidenceUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, eventFlowLegalLossless, losslessRecognizerGate,
    _nonEvidenceTransportReplay, _replayProvenanceLocalName, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row certificateGate ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eventFlow ∨ hsame row legalChannel ∨ hsame row lossless ∨
              hsame row recognizer ∨ hsame row certificateGate)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro certificateGate ⟨hsame_refl certificateGate, certificateGateUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg⟩
  }
  exact ⟨cert, eventFlowLegalLossless, losslessRecognizerGate, localNamePkg⟩

theorem GroundCompilerEventFlowAuditRouteCarrier_non_evidence_boundary
    [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row nonEvidence ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nonEvidence ∨ hsame row transport ∨ hsame row replay)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame ∧
        Cont nonEvidence transport replay ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_eventFlowUnary, _legalChannelUnary, _losslessUnary, _recognizerUnary,
    _certificateGateUnary, nonEvidenceUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _eventFlowLegalLossless, _losslessRecognizerGate,
    nonEvidenceTransportReplay, _replayProvenanceLocalName, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nonEvidence ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nonEvidence ∨ hsame row transport ∨ hsame row replay)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nonEvidence ⟨hsame_refl nonEvidence, nonEvidenceUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg⟩
  }
  exact ⟨cert, nonEvidenceTransportReplay, localNamePkg⟩

end BEDC.Derived.GroundCompilerEventFlowAuditRouteUp
