import BEDC.FKernel.Mark

namespace BEDC.GroundCompiler.EventFlow

open BEDC.FKernel.Mark

def DisplayAlphabet : Type := BMark

def RawEvent : Type := List DisplayAlphabet

def EventFlow : Type := List RawEvent

def EventBoundary (S : EventFlow) (i : Nat) : Prop :=
  i + 1 < S.length

def NonemptyEventFlow (S : EventFlow) : Prop :=
  exists w : RawEvent, exists rest : EventFlow, S = w :: rest

def erase (S : EventFlow) : List BMark :=
  S.flatten

inductive StrengthRole : Type where
  | seed
  | paperCert
  | checkedCert
  | bridgeCert

def strengthRank : StrengthRole -> Nat
  | StrengthRole.seed => 0
  | StrengthRole.paperCert => 1
  | StrengthRole.checkedCert => 2
  | StrengthRole.bridgeCert => 3

def StrengthRoleLT (a b : StrengthRole) : Prop :=
  strengthRank a < strengthRank b

def GeneratedStrengthRecognizer : Type := EventFlow

def DerivCertCandidateFlow : Type := EventFlow

def GeneratedRecognizer : Type := EventFlow

def RecognizerCandidateFlow : Type := EventFlow

def RecognitionRole : Type := EventFlow

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
  | hostDerivCert
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

def Recognizes
    (R : RecognizerCandidateFlow) (_rho : RecognitionRole) (S : EventFlow) :
    Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R S)

def RecognizesStrength
    (R : GeneratedStrengthRecognizer) (s : EventFlow) (_sigma : StrengthRole) :
    Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R s)

def StrengthEventFlow (s : EventFlow) : Prop :=
  exists R : GeneratedStrengthRecognizer,
    exists sigma : StrengthRole, RecognizesStrength R s sigma

def RecognizesPkg (R S : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R S) /\
    NonemptyEventFlow S

def RecognizedPackageFlow (S : EventFlow) : Prop :=
  exists R : GeneratedRecognizer, RecognizesPkg R S

def RecognizesNameCert (R S : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R S)

def RecognizedNameCertFlow (S : EventFlow) : Prop :=
  exists R : GeneratedRecognizer, RecognizesNameCert R S

def RecognizesClosureCert (R S : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R S)

def RecognizedClosureCertFlow (S : EventFlow) : Prop :=
  exists R : GeneratedRecognizer, RecognizesClosureCert R S

def RecognizesTheorem (R S : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R S) /\
    NonemptyEventFlow S

def RecognizedTheoremFlow (S : EventFlow) : Prop :=
  exists R : GeneratedRecognizer, RecognizesTheorem R S

def RecognizesCompiler (C : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow C)

def RecognizedCompilerFlow (C : EventFlow) : Prop :=
  RecognizesCompiler C

def CompilerBehavior : Type :=
  EventFlow -> EventFlow -> Prop

def BehaviorallyEquivalentCompilerFlow
    (behavior : CompilerBehavior) (C D : EventFlow) : Prop :=
  RecognizedCompilerFlow C /\
    RecognizedCompilerFlow D /\
    behavior C D /\
    behavior D C

def SelfHostingTarget (C : EventFlow) : Prop :=
  exists behavior : CompilerBehavior,
    BehaviorallyEquivalentCompilerFlow behavior C C

def AcceptedObjectFlow (S : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.certifiedExport S) /\
    NonemptyEventFlow S /\
    exists N C : EventFlow, RecognizedNameCertFlow N /\ RecognizedClosureCertFlow C

inductive StructuralHiddenInput : CompilerDatum -> Prop where
  | hostAST : StructuralHiddenInput CompilerDatum.hostAST
  | hostYAML : StructuralHiddenInput CompilerDatum.hostYAML
  | hostManifest : StructuralHiddenInput CompilerDatum.hostManifest
  | hostPkg : StructuralHiddenInput CompilerDatum.hostPkg
  | hostNameCert : StructuralHiddenInput CompilerDatum.hostNameCert
  | hostDerivCert : StructuralHiddenInput CompilerDatum.hostDerivCert
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

theorem package_not_primitive :
    Not (FormalCompilerInput CompilerDatum.hostPkg) :=
  structural_hidden_not_formal StructuralHiddenInput.hostPkg

theorem no_hidden_input {d : CompilerDatum} :
    FormalCompilerInput d ->
      (exists w : RawEvent, d = CompilerDatum.rawEvent w) \/
      (exists S : EventFlow, d = CompilerDatum.eventFlow S) \/
      (exists R : GeneratedRecognizer, exists S : EventFlow,
        d = CompilerDatum.recognizedFlow R S) \/
      (exists S : EventFlow, d = CompilerDatum.certifiedExport S) := by
  intro h
  cases h with
  | rawEvent w =>
      exact Or.inl ⟨w, rfl⟩
  | eventFlow S =>
      exact Or.inr (Or.inl ⟨S, rfl⟩)
  | recognizedFlow R S =>
      exact Or.inr (Or.inr (Or.inl ⟨R, S, rfl⟩))
  | certifiedExport S =>
      exact Or.inr (Or.inr (Or.inr ⟨S, rfl⟩))

theorem yaml_not_input :
    Not (FormalCompilerInput CompilerDatum.hostYAML) :=
  structural_hidden_not_formal StructuralHiddenInput.hostYAML

theorem ast_not_input :
    Not (FormalCompilerInput CompilerDatum.hostAST) :=
  structural_hidden_not_formal StructuralHiddenInput.hostAST

theorem self_hosting_target_recognized_compiler {C : EventFlow} :
    SelfHostingTarget C -> RecognizedCompilerFlow C := by
  intro h
  cases h with
  | intro _ heq =>
      exact heq.left

theorem accepted_export_requires_cert {S : EventFlow} :
    AcceptedObjectFlow S ->
      exists N C : EventFlow, RecognizedNameCertFlow N /\ RecognizedClosureCertFlow C := by
  intro h
  exact h.right.right

theorem empty_not_nonempty_event_flow :
    Not (NonemptyEventFlow []) := by
  intro h
  cases h with
  | intro w hrest =>
      cases hrest with
      | intro rest heq =>
          cases heq

theorem empty_not_recognized_package_flow :
    Not (RecognizedPackageFlow []) := by
  intro h
  cases h with
  | intro R hrec =>
      exact empty_not_nonempty_event_flow hrec.right

theorem empty_not_recognized_theorem_flow :
    Not (RecognizedTheoremFlow []) := by
  intro h
  cases h with
  | intro R hrec =>
      exact empty_not_nonempty_event_flow hrec.right

theorem empty_not_accepted_object_flow :
    Not (AcceptedObjectFlow []) := by
  intro h
  exact empty_not_nonempty_event_flow h.right.left

theorem code_not_acceptance :
    exists S : EventFlow,
      FormalCompilerInput (CompilerDatum.eventFlow S) /\ Not (AcceptedObjectFlow S) := by
  exact
    ⟨[], FormalCompilerInput.eventFlow [],
      empty_not_accepted_object_flow⟩

theorem readability_weaker_than_theoremhood :
    exists S : EventFlow,
      FormalCompilerInput (CompilerDatum.eventFlow S) /\
      Not (RecognizedTheoremFlow S) /\
      Not (RecognizedPackageFlow S) /\
      Not (AcceptedObjectFlow S) := by
  exact
    ⟨[], FormalCompilerInput.eventFlow [],
      empty_not_recognized_theorem_flow,
      empty_not_recognized_package_flow,
      empty_not_accepted_object_flow⟩

theorem event_flow_conservativity {S : EventFlow} {w : RawEvent}
    {m : DisplayAlphabet} :
    List.Mem w S -> List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

end BEDC.GroundCompiler.EventFlow
