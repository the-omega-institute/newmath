import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SemanticMotif

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

def ContiguousSubflow (M S : EventFlow) : Prop :=
  exists left right : EventFlow, S = List.append left (List.append M right)

inductive IndexedSubflow : EventFlow -> EventFlow -> Prop where
  | nil (S : EventFlow) : IndexedSubflow [] S
  | keep {w : RawEvent} {M S : EventFlow} :
      IndexedSubflow M S -> IndexedSubflow (w :: M) (w :: S)
  | skip {w : RawEvent} {M S : EventFlow} :
      IndexedSubflow M S -> IndexedSubflow M (w :: S)

def Subflow (M S : EventFlow) : Prop :=
  ContiguousSubflow M S \/ IndexedSubflow M S

def MotifCandidate (M S : EventFlow) : Prop :=
  Subflow M S

def GeneratedMotifRecognizer : Type := EventFlow

def MotifRole : Type := EventFlow

def FiniteRepetitionRole : MotifRole := [[BMark.b0]]

def ContinuationRole : MotifRole := [[BMark.b0, BMark.b0]]

def SealRole : MotifRole := [[BMark.b0, BMark.b1]]

def CarryRole : MotifRole := [[BMark.b1, BMark.b0]]

def ClassifierQuotientRole : MotifRole := [[BMark.b1, BMark.b0, BMark.b0]]

def LedgerCompressionRole : MotifRole := [[BMark.b1, BMark.b0, BMark.b1]]

def ReuseRole : MotifRole := [[BMark.b1, BMark.b1, BMark.b0]]

def BridgeRole : MotifRole := [[BMark.b1, BMark.b1, BMark.b1]]

def SourceLevelMotifArgs (S M : EventFlow) (mu : MotifRole) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow S) /\
    FormalCompilerInput (CompilerDatum.eventFlow M) /\
    FormalCompilerInput (CompilerDatum.eventFlow mu)

def RecognizesMotif
    (R : GeneratedMotifRecognizer) (S M : EventFlow) (mu : MotifRole) :
    Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow R) /\
    SourceLevelMotifArgs S M mu /\
    Subflow M S

def RecognizedMotifOccurrence
    (R : GeneratedMotifRecognizer) (S M : EventFlow) (mu : MotifRole) :
    Prop :=
  RecognizesMotif R S M mu

def MotifOccurrence
    (R : GeneratedMotifRecognizer) (S M : EventFlow) (mu : MotifRole) :
    Prop :=
  RecognizesMotif R S M mu

def MotifLedger
    (R : GeneratedMotifRecognizer) (S M : EventFlow) (mu : MotifRole)
    (L : EventFlow) :
    Prop :=
  RecognizesMotif R S M mu /\ Subflow L S

def RepeatRawEvent (x : RawEvent) : Nat -> RawEvent
  | 0 => x
  | n + 1 => List.append (RepeatRawEvent x n) x

def FiniteRepetitionPrefix (x : RawEvent) : Nat -> EventFlow
  | 0 => []
  | n + 1 => List.append (FiniteRepetitionPrefix x n) [RepeatRawEvent x n]

def FiniteRepetitionMotif
    (R : GeneratedMotifRecognizer) (S M : EventFlow) : Prop :=
  exists x : RawEvent,
    exists k : Nat,
      M = FiniteRepetitionPrefix x (k + 1) /\
        RecognizesMotif R S M FiniteRepetitionRole

def ContinuationMotif
    (R : GeneratedMotifRecognizer) (S M input result witness : EventFlow) :
    Prop :=
  RecognizesMotif R S M ContinuationRole /\
    Subflow input M /\
    Subflow result M /\
    Subflow witness M /\
    NonemptyEventFlow witness

def SealMotif
    (R : GeneratedMotifRecognizer)
    (S M stages boundary sealFlow ledgerFlow : EventFlow) : Prop :=
  RecognizesMotif R S M SealRole /\
    Subflow stages M /\
    Subflow boundary M /\
    Subflow sealFlow M /\
    Subflow ledgerFlow M /\
    NonemptyEventFlow sealFlow /\
    NonemptyEventFlow ledgerFlow

def CarryMotif
    (R : GeneratedMotifRecognizer)
    (S M preNormal normal ledgerFlow : EventFlow) : Prop :=
  RecognizesMotif R S M CarryRole /\
    Subflow preNormal M /\
    Subflow normal M /\
    Subflow ledgerFlow M /\
    NonemptyEventFlow preNormal /\
    NonemptyEventFlow normal /\
    NonemptyEventFlow ledgerFlow

def ClassifierQuotientMotif
    (R : GeneratedMotifRecognizer)
    (S M leftFlow rightFlow classifierFlow exactnessFlow
      failureFlow : EventFlow) : Prop :=
  RecognizesMotif R S M ClassifierQuotientRole /\
    Subflow leftFlow M /\
    Subflow rightFlow M /\
    Subflow classifierFlow M /\
    Subflow exactnessFlow M /\
    Subflow failureFlow M /\
    NonemptyEventFlow leftFlow /\
    NonemptyEventFlow rightFlow /\
    NonemptyEventFlow classifierFlow /\
    NonemptyEventFlow exactnessFlow

def LedgerCompressionMotif
    (R : GeneratedMotifRecognizer)
    (S M visibleFlow hiddenFlow ledgerFlow sourceMapFlow
      compressionSealFlow : EventFlow) : Prop :=
  RecognizesMotif R S M LedgerCompressionRole /\
    Subflow visibleFlow M /\
    Subflow hiddenFlow M /\
    Subflow ledgerFlow M /\
    Subflow sourceMapFlow M /\
    Subflow compressionSealFlow M /\
    NonemptyEventFlow visibleFlow /\
    NonemptyEventFlow hiddenFlow /\
    NonemptyEventFlow ledgerFlow /\
    NonemptyEventFlow sourceMapFlow /\
    NonemptyEventFlow compressionSealFlow

def ReuseMotif
    (R : GeneratedMotifRecognizer)
    (S M acceptedRefs transportWitness newSource classifierFlow ledgerFlow
      certificateFlow strengthBound : EventFlow) : Prop :=
  RecognizesMotif R S M ReuseRole /\
    Subflow acceptedRefs M /\
    Subflow transportWitness M /\
    Subflow newSource M /\
    Subflow classifierFlow M /\
    Subflow ledgerFlow M /\
    Subflow certificateFlow M /\
    Subflow strengthBound M /\
    NonemptyEventFlow acceptedRefs /\
    NonemptyEventFlow transportWitness /\
    NonemptyEventFlow newSource /\
    NonemptyEventFlow classifierFlow /\
    NonemptyEventFlow ledgerFlow /\
    NonemptyEventFlow certificateFlow /\
    NonemptyEventFlow strengthBound

def BridgeMotif
    (R : GeneratedMotifRecognizer)
    (S M bedcSource standardTargetDescription translationFlow soundnessFlow
      reflectionFlow noHostLeakLedger bridgeSeal : EventFlow) : Prop :=
  RecognizesMotif R S M BridgeRole /\
    Subflow bedcSource M /\
    Subflow standardTargetDescription M /\
    Subflow translationFlow M /\
    Subflow soundnessFlow M /\
    Subflow reflectionFlow M /\
    Subflow noHostLeakLedger M /\
    Subflow bridgeSeal M /\
    NonemptyEventFlow bedcSource /\
    NonemptyEventFlow standardTargetDescription /\
    NonemptyEventFlow translationFlow /\
    NonemptyEventFlow soundnessFlow /\
    NonemptyEventFlow noHostLeakLedger /\
    NonemptyEventFlow bridgeSeal

theorem no_external_motif_input
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    MotifOccurrence R S M mu ->
      FormalCompilerInput (CompilerDatum.eventFlow R) /\
        SourceLevelMotifArgs S M mu /\
        Subflow M S := by
  intro h
  exact h

theorem motif_recognition_source_level
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizesMotif R S M mu -> SourceLevelMotifArgs S M mu := by
  intro h
  exact h.right.left

theorem no_motif_without_ledger
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizesMotif R S M mu ->
      exists L : EventFlow, MotifLedger R S M mu L := by
  intro h
  exact ⟨M, h, h.right.right⟩

theorem motif_recognition_requires_generated_recognizer
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizedMotifOccurrence R S M mu ->
      FormalCompilerInput (CompilerDatum.eventFlow R) := by
  intro h
  exact h.left

theorem motif_analysis_decodes_first {c : List DisplayAlphabet} :
    LegalZStream c ->
      exists S : EventFlow,
        Decode c = some S /\
          FormalCompilerInput (CompilerDatum.eventFlow S) := by
  intro h
  cases legal_stream_completeness h with
  | intro S hS =>
      exact ⟨S, hS.left, FormalCompilerInput.eventFlow S⟩

theorem motif_recognition_preserves_code
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizesMotif R S M mu ->
      Compiles S (FlowEncoding S) /\ SourceLevelMotifArgs S M mu := by
  intro h
  exact ⟨rfl, h.right.left⟩

theorem motif_code_not_separate
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizesMotif R S M mu ->
      Compiles M (FlowEncoding M) /\ SourceLevelMotifArgs S M mu := by
  intro h
  exact ⟨rfl, h.right.left⟩

theorem motif_compile_decode_invariant
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizesMotif R S M mu ->
      exists T : EventFlow,
        Decode (FlowEncoding S) = some T /\ RecognizesMotif R T M mu := by
  intro h
  exact ⟨S, flow_level_round_trip S, h⟩

def MotifProfile
    (Rfam : GeneratedMotifRecognizer -> Prop) (S : EventFlow)
    (mu M L : EventFlow) : Prop :=
  exists R : GeneratedMotifRecognizer,
    Rfam R /\ RecognizesMotif R S M mu /\ MotifLedger R S M mu L

def MotifSupport
    (Rfam : GeneratedMotifRecognizer -> Prop) (S M L : EventFlow) :
    Prop :=
  exists mu : MotifRole, MotifProfile Rfam S mu M L

def MotifOverlap
    (Rfam : GeneratedMotifRecognizer -> Prop) (S T : EventFlow)
    (mu M L : EventFlow) : Prop :=
  MotifProfile Rfam S mu M L /\ MotifProfile Rfam T mu M L

def EventCommonPrefixLength (S T : EventFlow) (k : Nat) : Prop :=
  k <= S.length /\ k <= T.length /\ S.take k = T.take k

def RecognizedSemanticPrefix
    (R : GeneratedMotifRecognizer) (S T P : EventFlow) (mu : MotifRole) :
    Prop :=
  EventCommonPrefixLength S T P.length /\
    S.take P.length = P /\
    T.take P.length = P /\
    RecognizesMotif R S P mu /\
    RecognizesMotif R T P mu

theorem same_raw_prefix_not_unique_semantic_prefix :
    exists R S T P : EventFlow,
      EventCommonPrefixLength S T P.length /\
        S.take P.length = P /\
        T.take P.length = P /\
        RecognizesMotif R S P FiniteRepetitionRole /\
        RecognizesMotif R T P ContinuationRole /\
        Not (FiniteRepetitionRole = ContinuationRole) := by
  refine
    ⟨[], [[BMark.b0]], [[BMark.b0]], [[BMark.b0]], ?_⟩
  constructor
  · exact ⟨Nat.le_refl 1, Nat.le_refl 1, rfl⟩
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · exact
            ⟨FormalCompilerInput.eventFlow [],
              ⟨FormalCompilerInput.eventFlow [[BMark.b0]],
                FormalCompilerInput.eventFlow [[BMark.b0]],
                FormalCompilerInput.eventFlow FiniteRepetitionRole⟩,
              Or.inl ⟨[], [], rfl⟩⟩
        · constructor
          · exact
              ⟨FormalCompilerInput.eventFlow [],
                ⟨FormalCompilerInput.eventFlow [[BMark.b0]],
                  FormalCompilerInput.eventFlow [[BMark.b0]],
                  FormalCompilerInput.eventFlow ContinuationRole⟩,
                Or.inl ⟨[], [], rfl⟩⟩
          · intro h
            cases h

end BEDC.GroundCompiler.SemanticMotif
