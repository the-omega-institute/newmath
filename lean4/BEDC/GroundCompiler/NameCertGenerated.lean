import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.NameCertGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def NameCertRecognitionRelation
    (R : GeneratedRecognizer) (S N : EventFlow) : Prop :=
  RecognizesNameCert R S /\ FormalCompilerInput (CompilerDatum.eventFlow N)

def NameCertFlow (S N : EventFlow) : Prop :=
  exists R : GeneratedRecognizer, NameCertRecognitionRelation R S N

def NameCertRecognitionPreservingCompilation : Prop :=
  forall R : GeneratedRecognizer,
    forall S N : EventFlow,
      NameCertRecognitionRelation R S N ->
        exists S' : EventFlow,
          Decode (FlowEncoding S) = some S' /\
            NameCertRecognitionRelation R S' N

theorem channel_compilation_preserves_namecert_recognition :
    NameCertRecognitionPreservingCompilation := by
  intro R S N hRecognizes
  exact ⟨S, flow_level_round_trip S, hRecognizes⟩

end BEDC.GroundCompiler.NameCertGenerated
