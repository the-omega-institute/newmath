import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.NameCertGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def NameCandidateFlow : Type :=
  EventFlow

def NameCertCandidateFlow : Type :=
  EventFlow

def GeneratedNameCertRecognizer : Type :=
  GeneratedRecognizer

def NameCertRecognitionRelation
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (N : NameCandidateFlow) : Prop :=
  RecognizesNameCert R S /\ FormalCompilerInput (CompilerDatum.eventFlow N)

def NameCertFlow (S : NameCertCandidateFlow) (N : NameCandidateFlow) : Prop :=
  exists R : GeneratedNameCertRecognizer, NameCertRecognitionRelation R S N

def NameCertCode (S : NameCertCandidateFlow) (_N : NameCandidateFlow) :
    List DisplayAlphabet :=
  FlowEncoding S

def NameCertRecognitionPreservingCompilation : Prop :=
  forall R : GeneratedNameCertRecognizer,
    forall S : NameCertCandidateFlow,
    forall N : NameCandidateFlow,
      NameCertRecognitionRelation R S N ->
        exists S' : EventFlow,
          Decode (FlowEncoding S) = some S' /\
            NameCertRecognitionRelation R S' N

theorem no_external_namecert_input :
    Not (FormalCompilerInput CompilerDatum.hostNameCert) :=
  structural_hidden_not_formal StructuralHiddenInput.hostNameCert

theorem namecert_recognition_preserves_code
    {R : GeneratedNameCertRecognizer} {S : NameCertCandidateFlow}
    {N : NameCandidateFlow} :
    NameCertRecognitionRelation R S N ->
      LegalZStream (FlowEncoding S) /\ Decode (FlowEncoding S) = some S := by
  intro _
  exact ⟨flow_encoding_legal_zstream S, flow_level_round_trip S⟩

theorem namecert_code_not_separate
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} :
    NameCertFlow S N ->
      LegalZStream (NameCertCode S N) /\ Decode (NameCertCode S N) = some S := by
  intro _
  exact ⟨flow_encoding_legal_zstream S, flow_level_round_trip S⟩

theorem channel_compilation_preserves_namecert_recognition :
    NameCertRecognitionPreservingCompilation := by
  intro R S N hRecognizes
  exact ⟨S, flow_level_round_trip S, hRecognizes⟩

end BEDC.GroundCompiler.NameCertGenerated
