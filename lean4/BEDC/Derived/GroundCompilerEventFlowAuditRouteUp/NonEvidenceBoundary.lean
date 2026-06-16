import BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

namespace BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GroundCompilerEventFlowAuditRouteNonEvidenceBoundary [AskSetup] [PackageSetup]
    {eventFlow legalChannel lossless recognizer certificateGate nonEvidence transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow legalChannel lossless recognizer
        certificateGate nonEvidence transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row nonEvidence ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nonEvidence ∨ hsame row replay ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont nonEvidence transport replay ∧
              Cont replay provenance localName ∧ PkgSig bundle localName pkg)
          hsame ∧
        UnaryHistory nonEvidence ∧ UnaryHistory replay ∧ UnaryHistory localName ∧
          Cont nonEvidence transport replay ∧ Cont replay provenance localName ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_eventFlowUnary, _legalChannelUnary, _losslessUnary, _recognizerUnary,
    _certificateGateUnary, nonEvidenceUnary, _transportUnary, replayUnary,
    _provenanceUnary, localNameUnary, _eventFlowLegalLossless, _losslessRecognizerGate,
    nonEvidenceTransportReplay, replayProvenanceLocalName, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nonEvidence ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nonEvidence ∨ hsame row replay ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont nonEvidence transport replay ∧
              Cont replay provenance localName ∧ PkgSig bundle localName pkg)
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
      exact
        ⟨source.right, nonEvidenceTransportReplay, replayProvenanceLocalName, localNamePkg⟩
  }
  exact
    ⟨cert, nonEvidenceUnary, replayUnary, localNameUnary, nonEvidenceTransportReplay,
      replayProvenanceLocalName, localNamePkg⟩

end BEDC.Derived.GroundCompilerEventFlowAuditRouteUp
