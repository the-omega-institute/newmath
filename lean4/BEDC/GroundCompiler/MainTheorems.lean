import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.DerivCertGenerated
import BEDC.GroundCompiler.RecognizerFlows
import BEDC.GroundCompiler.SemanticMotif
import BEDC.GroundCompiler.SourceChannel
import BEDC.GroundCompiler.TheoremGenerated

namespace BEDC.GroundCompiler.MainTheorems

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.RecognizerFlows
open BEDC.GroundCompiler.SourceChannel

structure NoHiddenInputCompilerState where
  compile : EventFlow -> List DisplayAlphabet
  decode : List DisplayAlphabet -> Option EventFlow
  compile_legal : forall S : EventFlow, LegalZStream (compile S)
  decode_compile : forall S : EventFlow, decode (compile S) = some S
  legal_complete :
    forall c : List DisplayAlphabet,
      LegalZStream c ->
        exists S : EventFlow, decode c = some S /\ compile S = c
  hidden_excluded :
    forall d : CompilerDatum,
      StructuralHiddenInput d -> Not (FormalCompilerInput d)

def canonical_no_hidden_input_compiler_state : NoHiddenInputCompilerState where
  compile := FlowEncoding
  decode := Decode
  compile_legal := by
    intro S
    exact flow_encoding_legal_zstream S
  decode_compile := by
    intro S
    exact flow_level_round_trip S
  legal_complete := by
    intro c hLegal
    exact legal_stream_completeness hLegal
  hidden_excluded := by
    intro d hHidden
    exact structural_hidden_not_formal hHidden

def HiddenInput (d : CompilerDatum) : Prop :=
  StructuralHiddenInput d

theorem no_hidden_input
    (C : NoHiddenInputCompilerState) {d : CompilerDatum} :
    HiddenInput d -> Not (FormalCompilerInput d) := by
  intro hHidden
  exact C.hidden_excluded d hHidden

theorem channel_bijection :
    (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c ->
          exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c) := by
  exact channel_encoding_bijection

theorem channel_code_lossless {S T : EventFlow} :
    FlowEncoding S = FlowEncoding T -> S = T := by
  intro h
  have hS : Decode (FlowEncoding S) = some S := flow_level_round_trip S
  have hT : Decode (FlowEncoding T) = some T := flow_level_round_trip T
  rw [h] at hS
  have hSome : some S = some T := Eq.trans (Eq.symm hS) hT
  cases hSome
  rfl

theorem code_not_proof :
    exists c : List DisplayAlphabet,
      LegalZStream c /\
        Not (exists S : EventFlow,
          c = FlowEncoding S /\ RecognizedTheoremFlow S) := by
  exact legal_stream_not_theoremhood

theorem source_channel_separation :
    (forall S : EventFlow, LegalZStream (FlowEncoding S)) /\
      (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      Not (EventTerminator = EventEncoding [BMark.b1, BMark.b1]) /\
      exists c u : List DisplayAlphabet,
        LegalZStream c /\
          ContiguousSubstring u c /\
          Not (OccursAsDecodedEvent u c) := by
  exact layer_separation

theorem carry_not_channel_rewrite :
    LegalZStream (EventEncoding CarryPreNormal) /\
      Not (LegalZStream
        [BMark.b0, BMark.b1, BMark.b0, BMark.b1,
          BMark.b1, BMark.b0, BMark.b0]) := by
  exact no_channel_level_source_rewrite

def GeneratedStructure
    (RecognizesK : GeneratedRecognizer -> EventFlow -> Prop) : Prop :=
  exists R : GeneratedRecognizer, exists S : EventFlow,
    FormalCompilerInput (CompilerDatum.recognizedFlow R S) /\ RecognizesK R S

theorem structure_emergence :
    Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
      Not (FormalCompilerInput CompilerDatum.hostDerivCert) /\
      Not (FormalCompilerInput CompilerDatum.hostClosureCert) /\
      Not (FormalCompilerInput CompilerDatum.hostChapterPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
      Not (FormalCompilerInput CompilerDatum.hostManifest) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostNameCert
    · constructor
      · exact structural_hidden_not_formal StructuralHiddenInput.hostDerivCert
      · constructor
        · exact structural_hidden_not_formal StructuralHiddenInput.hostClosureCert
        · constructor
          · exact structural_hidden_not_formal StructuralHiddenInput.hostChapterPkg
          · constructor
            · exact
                structural_hidden_not_formal
                  StructuralHiddenInput.hostTheoremIdentifier
            · exact structural_hidden_not_formal StructuralHiddenInput.hostManifest

theorem yaml_ast_output_only :
    Not (FormalCompilerInput CompilerDatum.hostYAML) /\
      Not (FormalCompilerInput CompilerDatum.hostAST) /\
      Not (FormalCompilerInput CompilerDatum.hostManifest) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostYAML
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostAST
    · exact structural_hidden_not_formal StructuralHiddenInput.hostManifest

theorem recognizer_generatedness
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    FormalRecognitionEvidence R rho S ->
      CertifiedRecognizer R rho /\
        FormalCompilerInput (CompilerDatum.recognizedFlow R S) := by
  intro hEvidence
  exact ⟨hEvidence.left, hEvidence.right⟩

def CertificateMediatedExport (N s : EventFlow) : Prop :=
  DerivCertGenerated.AcceptGateFlow N s

def AcceptedExport (N s : EventFlow) : Prop :=
  CertificateMediatedExport N s

theorem accepted_export (N s : EventFlow) :
    AcceptedExport N s ↔ DerivCertGenerated.AcceptGateFlow N s := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem code_existence_not_export (N s : EventFlow) :
    exists c : List DisplayAlphabet,
      LegalZStream c /\
        Not (DerivCertGenerated.RecognizesAcceptanceCode c N s) := by
  exact ⟨[], DerivCertGenerated.code_existence_not_acceptance N s⟩

theorem motif_existence_not_export :
    Not (forall Rfam : SemanticMotif.GeneratedMotifRecognizer -> Prop,
      forall S mu M L : EventFlow,
        SemanticMotif.MotifProfile Rfam S mu M L -> AcceptedObjectFlow S) := by
  exact SemanticMotif.motif_analysis_cannot_license_mature_objects

def CanonicalTheoremFlow (T : EventFlow) : Prop :=
  exists R : TheoremGenerated.GeneratedTheoremRecognizer,
    TheoremGenerated.SoundTheoremFlow R T /\
      TheoremGenerated.SiteSoundTheoremRecognition R T

def TheoremCode (T : EventFlow) : List DisplayAlphabet :=
  FlowEncoding T

def LegalCanonicalTheoremCode (c : List DisplayAlphabet) : Prop :=
  exists T : EventFlow, CanonicalTheoremFlow T /\ c = TheoremCode T

theorem theorem_code_bijection :
    (forall T : EventFlow,
      CanonicalTheoremFlow T -> LegalCanonicalTheoremCode (TheoremCode T)) /\
      (forall T U : EventFlow,
        CanonicalTheoremFlow T ->
          CanonicalTheoremFlow U -> TheoremCode T = TheoremCode U -> T = U) /\
      (forall c : List DisplayAlphabet,
        LegalCanonicalTheoremCode c ->
          exists T : EventFlow,
            CanonicalTheoremFlow T /\ Decode c = some T /\ TheoremCode T = c) := by
  constructor
  · intro T hCanonical
    exact ⟨T, hCanonical, rfl⟩
  · constructor
    · intro T U _ _ hCode
      exact channel_code_lossless hCode
    · intro c hLegal
      cases hLegal with
      | intro T hT =>
          refine ⟨T, hT.left, ?_, hT.right.symm⟩
          rw [hT.right]
          exact flow_level_round_trip T

theorem proposition_not_theorem_code :
    exists R : TheoremGenerated.GeneratedTheoremRecognizer,
      exists statement T U : TheoremGenerated.TheoremCandidateFlow,
        Not (T = U) /\
          TheoremGenerated.TheoremRoleSubflow R T statement
            TheoremGenerated.TheoremRole.statement /\
          TheoremGenerated.TheoremRoleSubflow R U statement
            TheoremGenerated.TheoremRole.statement := by
  exact TheoremGenerated.same_statement_multiple_flows

theorem theorem_code_not_proof :
    exists c : List DisplayAlphabet,
      TheoremGenerated.LegalTheoremCode c /\
        exists T : TheoremGenerated.TheoremCandidateFlow,
          Decode c = some T /\
            (forall R : TheoremGenerated.GeneratedTheoremRecognizer,
              Not (TheoremGenerated.ProofSoundTheoremRecognition R T)) := by
  exact TheoremGenerated.theorem_code_is_not_proof

end BEDC.GroundCompiler.MainTheorems
