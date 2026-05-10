import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.TheoremProofPrototype

namespace BEDC.GroundCompiler.ChapterManuscript

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.TheoremProofPrototype

inductive P8FormalInput : Type where
  | channel (c : List DisplayAlphabet) (h : LegalZStream c)
  | eventFlow (S : EventFlow)

def P8InputSource (input : P8FormalInput) (S : EventFlow) : Prop :=
  match input with
  | P8FormalInput.channel c _ => Decode c = some S
  | P8FormalInput.eventFlow S0 => S = S0

inductive P8ExternalInput : Type where
  | chapterPackage
  | manuscriptFile
  | chapterTitle
  | sectionNumber
  | filePath
  | yaml
  | latex
  | markdown
  | tableOfContents

inductive P8InputRepresentation : Type where
  | formal (x : P8FormalInput)
  | external (x : P8ExternalInput)

inductive P8ReportDatum : Type where
  | decodedEventFlow (S : EventFlow)
  | chapterCandidate (C : EventFlow)
  | recognizedChapterFlow (R C : EventFlow)
  | chapterCode (C : EventFlow) (c : List DisplayAlphabet)
  | manuscriptCandidate (M : EventFlow)
  | recognizedManuscriptFlow (R M : EventFlow)
  | manuscriptCode (M : EventFlow) (c : List DisplayAlphabet)
  | missingField (owner field : EventFlow)
  | warning (w : EventFlow)
  | cannotClaim (cause : EventFlow)

def P8Output : Type :=
  List P8ReportDatum

structure ChapterManuscriptPrototype where
  p7 : TheoremProofPrototype
  definitionRecognizer : EventFlow
  lemmaRecognizer : EventFlow
  chapterRecognizer : EventFlow
  manuscriptRecognizer : EventFlow
  run : P8FormalInput -> P8Output
  chapterPackageNotFormal :
    forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.chapterPackage =
        P8InputRepresentation.formal x)
  manuscriptFileNotFormal :
    forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.manuscriptFile =
        P8InputRepresentation.formal x)

theorem chapter_manuscript_not_input :
    (forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.chapterPackage =
        P8InputRepresentation.formal x)) /\
      (forall x : P8FormalInput,
        Not (P8InputRepresentation.external P8ExternalInput.manuscriptFile =
          P8InputRepresentation.formal x)) := by
  constructor
  · intro x h
    cases h
  · intro x h
    cases h

end BEDC.GroundCompiler.ChapterManuscript
