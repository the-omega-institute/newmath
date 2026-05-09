import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SemanticMotif

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

end BEDC.GroundCompiler.SemanticMotif
