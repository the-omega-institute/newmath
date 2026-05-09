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

theorem motif_compile_decode_invariant
    {R : GeneratedMotifRecognizer} {S M : EventFlow} {mu : MotifRole} :
    RecognizesMotif R S M mu ->
      exists T : EventFlow,
        Decode (FlowEncoding S) = some T /\ RecognizesMotif R T M mu := by
  intro h
  exact ⟨S, flow_level_round_trip S, h⟩

end BEDC.GroundCompiler.SemanticMotif
