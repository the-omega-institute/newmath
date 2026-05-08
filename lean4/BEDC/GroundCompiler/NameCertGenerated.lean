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

def SourceSubflow (part whole : EventFlow) : Prop :=
  exists before after : EventFlow, whole = List.append before (List.append part after)

inductive NameCertFieldRole : Type where
  | source
  | pattern
  | classifier
  | stability
  | ledger

def NameCertFieldSubflow
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (_role : NameCertFieldRole) (part : EventFlow) : Prop :=
  RecognizesNameCert R S /\ SourceSubflow part S

def NameCertSealSubflow
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (sealFlow : EventFlow) : Prop :=
  RecognizesNameCert R S /\ SourceSubflow sealFlow S

def CompleteFiveFieldRecognition
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow) : Prop :=
  exists source pattern classifier stability ledger sealFlow : EventFlow,
    NameCertFieldSubflow R S NameCertFieldRole.source source /\
      NameCertFieldSubflow R S NameCertFieldRole.pattern pattern /\
      NameCertFieldSubflow R S NameCertFieldRole.classifier classifier /\
      NameCertFieldSubflow R S NameCertFieldRole.stability stability /\
      NameCertFieldSubflow R S NameCertFieldRole.ledger ledger /\
      NameCertSealSubflow R S sealFlow

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
