import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SourceChannel

namespace BEDC.GroundCompiler.MainTheorems

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
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

end BEDC.GroundCompiler.MainTheorems
