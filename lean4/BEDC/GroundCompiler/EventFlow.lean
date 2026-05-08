import BEDC.FKernel.Mark

namespace BEDC.GroundCompiler.EventFlow

open BEDC.FKernel.Mark

def RawEvent : Type := List BMark

def EventFlow : Type := List RawEvent

def EventBoundary (S : EventFlow) (i : Nat) : Prop :=
  i + 1 < S.length

def erase (S : EventFlow) : List BMark :=
  S.flatten

def GeneratedRecognizer : Type := EventFlow

inductive CompilerDatum : Type where
  | rawEvent (w : RawEvent)
  | eventFlow (S : EventFlow)
  | recognizedFlow (R : GeneratedRecognizer) (S : EventFlow)
  | certifiedExport (S : EventFlow)
  | hostAST
  | hostYAML
  | hostManifest
  | hostPkg
  | hostNameCert
  | hostClosureCert
  | hostTheoremIdentifier
  | hostObjectName
  | hostTypeTag
  | hostModeTag
  | hostOpcode
  | hostArityTable
  | hostParserState

inductive FormalCompilerInput : CompilerDatum -> Prop where
  | rawEvent (w : RawEvent) :
      FormalCompilerInput (CompilerDatum.rawEvent w)
  | eventFlow (S : EventFlow) :
      FormalCompilerInput (CompilerDatum.eventFlow S)
  | recognizedFlow (R : GeneratedRecognizer) (S : EventFlow) :
      FormalCompilerInput (CompilerDatum.recognizedFlow R S)
  | certifiedExport (S : EventFlow) :
      FormalCompilerInput (CompilerDatum.certifiedExport S)

inductive StructuralHiddenInput : CompilerDatum -> Prop where
  | hostAST : StructuralHiddenInput CompilerDatum.hostAST
  | hostYAML : StructuralHiddenInput CompilerDatum.hostYAML
  | hostManifest : StructuralHiddenInput CompilerDatum.hostManifest
  | hostPkg : StructuralHiddenInput CompilerDatum.hostPkg
  | hostNameCert : StructuralHiddenInput CompilerDatum.hostNameCert
  | hostClosureCert : StructuralHiddenInput CompilerDatum.hostClosureCert
  | hostTheoremIdentifier :
      StructuralHiddenInput CompilerDatum.hostTheoremIdentifier
  | hostObjectName : StructuralHiddenInput CompilerDatum.hostObjectName
  | hostTypeTag : StructuralHiddenInput CompilerDatum.hostTypeTag
  | hostModeTag : StructuralHiddenInput CompilerDatum.hostModeTag
  | hostOpcode : StructuralHiddenInput CompilerDatum.hostOpcode
  | hostArityTable : StructuralHiddenInput CompilerDatum.hostArityTable
  | hostParserState : StructuralHiddenInput CompilerDatum.hostParserState

theorem erase_not_injective :
    exists S1 S2 : EventFlow, Not (S1 = S2) /\ erase S1 = erase S2 := by
  refine
    ⟨[[BMark.b0], [BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b0]],
      [[BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b0, BMark.b0]], ?_⟩
  constructor
  · intro h
    cases h
  · rfl

theorem input_not_bare_bitstream (decode : List BMark -> EventFlow) :
    Not (forall S : EventFlow, decode (erase S) = S) := by
  intro h
  have hS1 :
      decode (erase [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0]]) =
      [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0]] :=
    h [[BMark.b0], [BMark.b0, BMark.b0],
      [BMark.b0, BMark.b0, BMark.b0]]
  have hS2 :
      decode (erase [[BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0]]) =
      [[BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0]] :=
    h [[BMark.b0, BMark.b0],
      [BMark.b0, BMark.b0, BMark.b0, BMark.b0]]
  have eqFlows :
      [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0]] =
      [[BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0]] :=
    Eq.trans (Eq.symm hS1) hS2
  cases eqFlows

theorem structural_hidden_not_formal {d : CompilerDatum} :
    StructuralHiddenInput d -> Not (FormalCompilerInput d) := by
  intro hHidden hFormal
  cases hHidden <;> cases hFormal

theorem yaml_not_input :
    Not (FormalCompilerInput CompilerDatum.hostYAML) :=
  structural_hidden_not_formal StructuralHiddenInput.hostYAML

theorem ast_not_input :
    Not (FormalCompilerInput CompilerDatum.hostAST) :=
  structural_hidden_not_formal StructuralHiddenInput.hostAST

end BEDC.GroundCompiler.EventFlow
