import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.NameCertGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def NameCandidateFlow : Type :=
  EventFlow

def NameCertCandidateFlow : Type :=
  EventFlow

def NameCertRecognitionRelation
    (R : GeneratedRecognizer) (S : NameCertCandidateFlow)
    (N : NameCandidateFlow) : Prop :=
  RecognizesNameCert R S /\ FormalCompilerInput (CompilerDatum.eventFlow N)

def NameCertFlow (S : NameCertCandidateFlow) (N : NameCandidateFlow) : Prop :=
  exists R : GeneratedRecognizer, NameCertRecognitionRelation R S N

def NameCertRecognitionPreservingCompilation : Prop :=
  forall R : GeneratedRecognizer,
    forall S : NameCertCandidateFlow,
    forall N : NameCandidateFlow,
      NameCertRecognitionRelation R S N ->
        exists S' : EventFlow,
          Decode (FlowEncoding S) = some S' /\
            NameCertRecognitionRelation R S' N

theorem no_external_namecert_input :
    Not (FormalCompilerInput CompilerDatum.hostNameCert) :=
  structural_hidden_not_formal StructuralHiddenInput.hostNameCert

theorem channel_compilation_preserves_namecert_recognition :
    NameCertRecognitionPreservingCompilation := by
  intro R S N hRecognizes
  exact ⟨S, flow_level_round_trip S, hRecognizes⟩

end BEDC.GroundCompiler.NameCertGenerated
