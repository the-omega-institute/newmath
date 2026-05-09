import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.AnalysisPipeline

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

inductive AnalysisInput : Type where
  | channel (c : List DisplayAlphabet) : LegalZStream c -> AnalysisInput
  | source (S : EventFlow) : AnalysisInput

def AnalysisInputSource (input : AnalysisInput) (S : EventFlow) : Prop :=
  match input with
  | AnalysisInput.channel c _ => Decode c = some S
  | AnalysisInput.source S0 => S = S0

theorem decode_first_analysis {c : List DisplayAlphabet} :
    LegalZStream c -> exists S : EventFlow, Decode c = some S := by
  intro h
  cases legal_stream_completeness h with
  | intro S hS =>
      exact ⟨S, hS.left⟩

def AnalysisProtocolCandidateFlow : Type := EventFlow

def GeneratedAnalysisProtocolRecognizer : Type := EventFlow

def RecognizesAnalysisProtocol
    (R : GeneratedAnalysisProtocolRecognizer)
    (P : AnalysisProtocolCandidateFlow) : Prop :=
  NonemptyEventFlow R /\ NonemptyEventFlow P

def RecognizedAnalysisProtocolFlow
    (P : AnalysisProtocolCandidateFlow) : Prop :=
  exists R : GeneratedAnalysisProtocolRecognizer,
    RecognizesAnalysisProtocol R P

inductive FormalAnalysisProtocol :
    AnalysisProtocolCandidateFlow -> Prop where
  | recognized {R : GeneratedAnalysisProtocolRecognizer}
      {P : AnalysisProtocolCandidateFlow} :
      RecognizesAnalysisProtocol R P -> FormalAnalysisProtocol P

theorem unrecognized_protocol_rejected
    {P : AnalysisProtocolCandidateFlow} :
    Not (exists R : GeneratedAnalysisProtocolRecognizer,
      RecognizesAnalysisProtocol R P) ->
      Not (FormalAnalysisProtocol P) := by
  intro hMissing hFormal
  cases hFormal with
  | recognized hRec =>
      exact hMissing ⟨_, hRec⟩

end BEDC.GroundCompiler.AnalysisPipeline
