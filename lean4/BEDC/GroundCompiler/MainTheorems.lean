import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.MainTheorems

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

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

end BEDC.GroundCompiler.MainTheorems
