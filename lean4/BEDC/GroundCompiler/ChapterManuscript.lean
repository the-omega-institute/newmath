import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.ChapterFlow
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

theorem no_incomplete_chapter
    {C : ChapterFlow.ChapterCandidateFlow} :
    ChapterFlow.ChapterFlow C ->
      exists R : ChapterFlow.GeneratedChapterRecognizer,
        ChapterFlow.CompleteChapterRecognition R C := by
  intro hChapter
  exact ChapterFlow.no_chapter_without_complete_recognition hChapter

theorem incomplete_chapter_candidate_not_flow
    {C : ChapterFlow.ChapterCandidateFlow} :
    (forall R : ChapterFlow.GeneratedChapterRecognizer,
      Not (ChapterFlow.CompleteChapterRecognition R C)) ->
    Not (ChapterFlow.ChapterFlow C) := by
  intro hIncomplete
  exact ChapterFlow.incomplete_chapter_flow_not_chapter hIncomplete

theorem title_alone_not_chapter
    {R : ChapterFlow.GeneratedChapterRecognizer}
    {C T : ChapterFlow.ChapterCandidateFlow} :
    ChapterFlow.ChapStart R C T ->
      (forall R' : ChapterFlow.GeneratedChapterRecognizer,
        Not (ChapterFlow.CompleteChapterRecognition R' C)) ->
      Not (ChapterFlow.ChapterFlow C) := by
  intro hStart hIncomplete
  exact ChapterFlow.title_alone_not_chapter hStart hIncomplete

theorem theorem_list_alone_not_chapter
    {R : ChapterFlow.GeneratedChapterRecognizer}
    {C T : ChapterFlow.ChapterCandidateFlow} :
    ChapterFlow.ChapTheorems R C T ->
      (forall R' : ChapterFlow.GeneratedChapterRecognizer,
        Not (ChapterFlow.CompleteChapterRecognition R' C)) ->
      Not (ChapterFlow.ChapterFlow C) := by
  intro hTheorems hIncomplete
  exact ChapterFlow.theorem_list_alone_not_chapter hTheorems hIncomplete

def SoundChapterFlow
    (R : ChapterFlow.GeneratedChapterRecognizer)
    (C : ChapterFlow.ChapterCandidateFlow) : Prop :=
  ChapterFlow.SoundRecognizedChapterFlow R C

def ChapterSoundnessClauses
    (R : ChapterFlow.GeneratedChapterRecognizer)
    (C : ChapterFlow.ChapterCandidateFlow) : Prop :=
  ChapterFlow.DependencySound R C /\
    ChapterFlow.DefinitionSound R C /\
    ChapterFlow.TheoremSound R C /\
    ChapterFlow.ProofSound R C /\
    ChapterFlow.CertificateSound R C /\
    ChapterFlow.LedgerSound R C /\
    ChapterFlow.CannotClaimSound R C /\
    ChapterFlow.StatusSound R C

theorem sound_chapter_code
    {R : ChapterFlow.GeneratedChapterRecognizer}
    {C : ChapterFlow.ChapterCandidateFlow} :
    SoundChapterFlow R C ->
      ChapterFlow.ChapterCode C = FlowEncoding C /\
        Decode (ChapterFlow.ChapterCode C) = some C := by
  intro _
  constructor
  · rfl
  · exact ChapterFlow.chapter_code_round_trip C

theorem chapter_code_injective
    {C D : ChapterFlow.ChapterCandidateFlow} :
    ChapterFlow.ChapterCode C = ChapterFlow.ChapterCode D -> C = D := by
  intro hCode
  exact ChapterFlow.chapter_code_injective hCode

theorem chapter_code_not_topic
    {C D : ChapterFlow.ChapterCandidateFlow} :
    ChapterFlow.ChapterCode C = ChapterFlow.ChapterCode D -> C = D := by
  intro hCode
  exact ChapterFlow.chapter_code_injective hCode

def ManuscriptCandidateFlow : Type :=
  EventFlow

def GeneratedManuscriptRecognizer : Type :=
  EventFlow

def RecognizesManuscript
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R M) /\
    NonemptyEventFlow M

def ManuscriptRole
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  RecognizesManuscript R M /\
    FormalCompilerInput (CompilerDatum.eventFlow X) /\
    NonemptyEventFlow X

def MsStart
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsChapters
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsDependencies
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsNotation
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsCertificates
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsLedger
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsCannotClaims
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsStatus
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsBridgeObligations
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsImplementationTargets
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def MsSeal
    (R : GeneratedManuscriptRecognizer) (M X : ManuscriptCandidateFlow) : Prop :=
  ManuscriptRole R M X

def ManuscriptSubflows
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 sigmaM : ManuscriptCandidateFlow,
    MsStart R M M0 /\
    MsChapters R M M1 /\
    MsDependencies R M M2 /\
    MsNotation R M M3 /\
    MsCertificates R M M4 /\
    MsLedger R M M5 /\
    MsCannotClaims R M M6 /\
    MsStatus R M M7 /\
    MsBridgeObligations R M M8 /\
    MsImplementationTargets R M M9 /\
    MsSeal R M sigmaM

def CompleteManuscriptRecognition
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  RecognizesManuscript R M /\ ManuscriptSubflows R M

def ManuscriptFlow (M : ManuscriptCandidateFlow) : Prop :=
  exists R : GeneratedManuscriptRecognizer, CompleteManuscriptRecognition R M

theorem no_incomplete_manuscript {M : ManuscriptCandidateFlow} :
    ManuscriptFlow M ->
      exists R : GeneratedManuscriptRecognizer,
        CompleteManuscriptRecognition R M := by
  intro hManuscript
  exact hManuscript

theorem incomplete_manuscript_flow_not_manuscript {M : ManuscriptCandidateFlow} :
    (forall R : GeneratedManuscriptRecognizer,
      Not (CompleteManuscriptRecognition R M)) ->
    Not (ManuscriptFlow M) := by
  intro hIncomplete hManuscript
  cases hManuscript with
  | intro R hComplete =>
      exact hIncomplete R hComplete

theorem table_of_contents_alone_not_manuscript
    {R : GeneratedManuscriptRecognizer} {M T : ManuscriptCandidateFlow} :
    MsChapters R M T ->
      (forall R' : GeneratedManuscriptRecognizer,
        Not (CompleteManuscriptRecognition R' M)) ->
      Not (ManuscriptFlow M) := by
  intro _ hIncomplete
  exact incomplete_manuscript_flow_not_manuscript hIncomplete

end BEDC.GroundCompiler.ChapterManuscript
