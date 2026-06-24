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

theorem GroundCompilerEventFlowAuditRouteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg ->
      Cont certificateGate replay auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row eventFlow ∨ hsame row legalChannel ∨ hsame row lossless ∨
                  hsame row recognizer ∨ hsame row certificateGate ∨ hsame row nonEvidence ∨
                    hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row auditRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont certificateGate replay auditRead ∧
                  PkgSig bundle auditRead pkg ∧ PkgSig bundle localName pkg)
              hsame ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier certificateReplayAudit auditPkg
  obtain ⟨_eventFlowUnary, _legalChannelUnary, _losslessUnary, _recognizerUnary,
    certificateGateUnary, _nonEvidenceUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _eventFlowLegalLossless, _losslessRecognizerGate,
    _nonEvidenceTransportReplay, _replayProvenanceLocalName, localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed certificateGateUnary replayUnary certificateReplayAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eventFlow ∨ hsame row legalChannel ∨ hsame row lossless ∨
              hsame row recognizer ∨ hsame row certificateGate ∨ hsame row nonEvidence ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont certificateGate replay auditRead ∧
              PkgSig bundle auditRead pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, certificateReplayAudit, auditPkg, localNamePkg⟩
  }
  exact ⟨cert, auditUnary⟩

theorem GroundCompilerEventFlowAuditRouteCarrier_classifier_stability [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg ->
      hsame stableRead certificateGate ->
        Cont lossless recognizer certificateGate ->
          SemanticNameCert
              (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row lossless ∨ hsame row recognizer ∨ hsame row certificateGate ∨
                  hsame row stableRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont lossless recognizer certificateGate ∧
                  PkgSig bundle localName pkg)
              hsame ∧ UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier stableCertificate losslessRecognizerGate
  obtain ⟨_eventFlowUnary, _legalChannelUnary, _losslessUnary, _recognizerUnary,
    certificateGateUnary, _nonEvidenceUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _eventFlowLegalLossless, _losslessRecognizerGate,
    _nonEvidenceTransportReplay, _replayProvenanceLocalName, localNamePkg⟩ := carrier
  have stableUnary : UnaryHistory stableRead :=
    unary_transport_symm certificateGateUnary stableCertificate
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lossless ∨ hsame row recognizer ∨ hsame row certificateGate ∨
              hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lossless recognizer certificateGate ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stableRead ⟨hsame_refl stableRead, stableUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, losslessRecognizerGate, localNamePkg⟩
  }
  exact ⟨cert, stableUnary⟩

theorem GroundCompilerEventFlowAuditRouteCarrier_certificate_gate_exhaustion
    [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName gateExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg →
      Cont certificateGate nonEvidence gateExport →
        PkgSig bundle gateExport pkg →
          SemanticNameCert
              (fun row : BHist => hsame row gateExport ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row eventFlow ∨ hsame row legalChannel ∨ hsame row lossless ∨
                  hsame row recognizer ∨ hsame row certificateGate ∨ hsame row nonEvidence ∨
                    hsame row gateExport)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont eventFlow legalChannel lossless ∧
                  Cont lossless recognizer certificateGate ∧
                    Cont certificateGate nonEvidence gateExport ∧ PkgSig bundle gateExport pkg)
              hsame ∧ UnaryHistory gateExport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier certificateNonEvidenceGate gatePkg
  obtain ⟨_eventFlowUnary, _legalChannelUnary, _losslessUnary, _recognizerUnary,
    certificateGateUnary, nonEvidenceUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, eventFlowLegalLossless, losslessRecognizerGate,
    _nonEvidenceTransportReplay, _replayProvenanceLocalName, _localNamePkg⟩ := carrier
  have gateUnary : UnaryHistory gateExport :=
    unary_cont_closed certificateGateUnary nonEvidenceUnary certificateNonEvidenceGate
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gateExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eventFlow ∨ hsame row legalChannel ∨ hsame row lossless ∨
              hsame row recognizer ∨ hsame row certificateGate ∨ hsame row nonEvidence ∨
                hsame row gateExport)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont eventFlow legalChannel lossless ∧
              Cont lossless recognizer certificateGate ∧
                Cont certificateGate nonEvidence gateExport ∧ PkgSig bundle gateExport pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gateExport ⟨hsame_refl gateExport, gateUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, eventFlowLegalLossless, losslessRecognizerGate,
          certificateNonEvidenceGate, gatePkg⟩
  }
  exact ⟨cert, gateUnary⟩

end BEDC.Derived.GroundCompilerEventFlowAuditRouteUp
