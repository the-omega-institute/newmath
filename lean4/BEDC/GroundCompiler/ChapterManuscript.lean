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

inductive P8FieldStatus : Type where
  | present
  | missing
  | candidateOnly

structure ChapterP8FieldStatus where
  start : P8FieldStatus
  dependencies : P8FieldStatus
  definitions : P8FieldStatus
  lemmas : P8FieldStatus
  theorems : P8FieldStatus
  proofs : P8FieldStatus
  certificates : P8FieldStatus
  ledger : P8FieldStatus
  cannotClaims : P8FieldStatus
  chapterStatus : P8FieldStatus
  chapterSeal : P8FieldStatus

structure ManuscriptP8FieldStatus where
  start : P8FieldStatus
  chapters : P8FieldStatus
  dependencies : P8FieldStatus
  notationFlow : P8FieldStatus
  certificates : P8FieldStatus
  ledger : P8FieldStatus
  cannotClaims : P8FieldStatus
  manuscriptStatus : P8FieldStatus
  bridgeObligations : P8FieldStatus
  implementationTargets : P8FieldStatus
  manuscriptSeal : P8FieldStatus

structure ChapterP8FieldStatusEntry where
  chapter : ChapterFlow.ChapterCandidateFlow
  fields : ChapterP8FieldStatus

structure ManuscriptP8FieldStatusEntry where
  manuscript : EventFlow
  fields : ManuscriptP8FieldStatus

inductive P8CannotClaimKind : Type where
  | titleAloneNotChapter
  | theoremListAloneNotChapter
  | tableOfContentsAloneNotManuscript
  | chapterCodeNotTheoremProof
  | manuscriptCodeNotAllClaimsAccepted
  | soundChapterNotAllMentionedObjectsAccepted
  | soundManuscriptNotAllBridgeObligationsDischarged
  | missingGlobalCannotClaimRegistryBlocksSoundness
  | implementationTargetListNotCheckedImplementation
  | manuscriptTopicEqualityNotCodeEquality

def P8CannotClaimAnnotations : Type :=
  List P8CannotClaimKind

def CompleteP8CannotClaimAnnotations
    (claims : P8CannotClaimAnnotations) : Prop :=
  List.Mem P8CannotClaimKind.titleAloneNotChapter claims /\
    List.Mem P8CannotClaimKind.theoremListAloneNotChapter claims /\
    List.Mem P8CannotClaimKind.tableOfContentsAloneNotManuscript claims /\
    List.Mem P8CannotClaimKind.chapterCodeNotTheoremProof claims /\
    List.Mem P8CannotClaimKind.manuscriptCodeNotAllClaimsAccepted claims /\
    List.Mem P8CannotClaimKind.soundChapterNotAllMentionedObjectsAccepted claims /\
    List.Mem
      P8CannotClaimKind.soundManuscriptNotAllBridgeObligationsDischarged claims /\
    List.Mem
      P8CannotClaimKind.missingGlobalCannotClaimRegistryBlocksSoundness claims /\
    List.Mem P8CannotClaimKind.implementationTargetListNotCheckedImplementation
      claims /\
    List.Mem P8CannotClaimKind.manuscriptTopicEqualityNotCodeEquality claims

structure P8Report where
  outputView : P8Output
  chapterFieldStatus : List ChapterP8FieldStatusEntry
  manuscriptFieldStatus : List ManuscriptP8FieldStatusEntry
  cannotClaims : P8CannotClaimAnnotations

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

def ManuscriptChapterSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M1 : ManuscriptCandidateFlow, MsChapters R M M1

def ManuscriptDependencySound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M2 : ManuscriptCandidateFlow, MsDependencies R M M2

def ManuscriptNotationSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M3 : ManuscriptCandidateFlow, MsNotation R M M3

def ManuscriptCertificateSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M4 : ManuscriptCandidateFlow, MsCertificates R M M4

def ManuscriptLedgerSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M5 : ManuscriptCandidateFlow, MsLedger R M M5

def ManuscriptCannotClaimSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M6 : ManuscriptCandidateFlow, MsCannotClaims R M M6

def ManuscriptStatusSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M7 : ManuscriptCandidateFlow, MsStatus R M M7

def ManuscriptImplementationSound
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  exists M9 : ManuscriptCandidateFlow, MsImplementationTargets R M M9

def ManuscriptSoundnessClauses
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  ManuscriptChapterSound R M /\
    ManuscriptDependencySound R M /\
    ManuscriptNotationSound R M /\
    ManuscriptCertificateSound R M /\
    ManuscriptLedgerSound R M /\
    ManuscriptCannotClaimSound R M /\
    ManuscriptStatusSound R M /\
    ManuscriptImplementationSound R M

def SoundManuscriptFlow
    (R : GeneratedManuscriptRecognizer) (M : ManuscriptCandidateFlow) : Prop :=
  CompleteManuscriptRecognition R M /\ ManuscriptSoundnessClauses R M

def ManuscriptCode (M : ManuscriptCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding M

theorem manuscript_code_round_trip (M : ManuscriptCandidateFlow) :
    Decode (ManuscriptCode M) = some M :=
  flow_level_round_trip M

theorem sound_manuscript_code
    {R : GeneratedManuscriptRecognizer} {M : ManuscriptCandidateFlow} :
    SoundManuscriptFlow R M ->
      ManuscriptCode M = FlowEncoding M /\
        Decode (ManuscriptCode M) = some M := by
  intro _
  constructor
  · rfl
  · exact manuscript_code_round_trip M

theorem manuscript_code_injective {M N : ManuscriptCandidateFlow} :
    ManuscriptCode M = ManuscriptCode N -> M = N := by
  intro hCode
  have hDecode : Decode (ManuscriptCode M) = Decode (ManuscriptCode N) :=
    congrArg Decode hCode
  rw [manuscript_code_round_trip M, manuscript_code_round_trip N] at hDecode
  cases hDecode
  rfl

theorem manuscript_code_not_topic {M N : ManuscriptCandidateFlow} :
    ManuscriptCode M = ManuscriptCode N -> M = N := by
  intro hCode
  exact manuscript_code_injective hCode

def SoundP8Report (report : P8Report) : Prop :=
  (forall C code,
    List.Mem (P8ReportDatum.chapterCode C code) report.outputView ->
      exists R : ChapterFlow.GeneratedChapterRecognizer,
        SoundChapterFlow R C /\ code = ChapterFlow.ChapterCode C) /\
    (forall M code,
      List.Mem (P8ReportDatum.manuscriptCode M code) report.outputView ->
        exists R : GeneratedManuscriptRecognizer,
          SoundManuscriptFlow R M /\ code = ManuscriptCode M) /\
    (forall R C,
      List.Mem (P8ReportDatum.recognizedChapterFlow R C) report.outputView ->
        ChapterFlow.CompleteChapterRecognition R C) /\
    (forall R M,
      List.Mem (P8ReportDatum.recognizedManuscriptFlow R M) report.outputView ->
        CompleteManuscriptRecognition R M)

structure P8AuditChecklist
    (prototype : ChapterManuscriptPrototype) (report : P8Report) where
  p7Audit : P7AuditChecklist prototype.p7
  chapterPackageNotFormal :
    forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.chapterPackage =
        P8InputRepresentation.formal x)
  manuscriptFileNotFormal :
    forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.manuscriptFile =
        P8InputRepresentation.formal x)
  soundReport : SoundP8Report report
  cannotClaimAnnotationsComplete :
    CompleteP8CannotClaimAnnotations report.cannotClaims

structure P8Adequate
    (prototype : ChapterManuscriptPrototype) (report : P8Report) where
  audit : P8AuditChecklist prototype report
  p7Adequate : P7AdequatePrototype prototype.p7
  soundReport : SoundP8Report report
  cannotClaimAnnotationsComplete :
    CompleteP8CannotClaimAnnotations report.cannotClaims
  chapterPackageNotFormal :
    forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.chapterPackage =
        P8InputRepresentation.formal x)
  manuscriptFileNotFormal :
    forall x : P8FormalInput,
      Not (P8InputRepresentation.external P8ExternalInput.manuscriptFile =
        P8InputRepresentation.formal x)

theorem p8_adequacy
    {prototype : ChapterManuscriptPrototype} {report : P8Report} :
    P8AuditChecklist prototype report -> P8Adequate prototype report := by
  intro hAudit
  exact
    { audit := hAudit,
      p7Adequate := p7_adequacy hAudit.p7Audit,
      soundReport := hAudit.soundReport,
      cannotClaimAnnotationsComplete :=
        hAudit.cannotClaimAnnotationsComplete,
      chapterPackageNotFormal := hAudit.chapterPackageNotFormal,
      manuscriptFileNotFormal := hAudit.manuscriptFileNotFormal }

inductive P8HigherReportDatum : P8ReportDatum -> Prop

def P8HigherAdequacy (report : P8Report) : Prop :=
  exists datum : P8ReportDatum,
    List.Mem datum report.outputView /\ P8HigherReportDatum datum

theorem p8_adequacy_not_higher {report : P8Report} :
    Not (P8HigherAdequacy report) := by
  intro hHigher
  cases hHigher with
  | intro _ hDatum =>
      cases hDatum.right

theorem sound_p8_report {report : P8Report} :
    SoundP8Report report ->
      (forall C code,
        List.Mem (P8ReportDatum.chapterCode C code) report.outputView ->
          exists R : ChapterFlow.GeneratedChapterRecognizer,
            SoundChapterFlow R C /\ code = ChapterFlow.ChapterCode C) /\
        (forall M code,
          List.Mem (P8ReportDatum.manuscriptCode M code) report.outputView ->
            exists R : GeneratedManuscriptRecognizer,
              SoundManuscriptFlow R M /\ code = ManuscriptCode M) := by
  intro hSound
  exact ⟨hSound.left, hSound.right.left⟩

theorem manuscript_code_flow_mediated
    {report : P8Report} {M : ManuscriptCandidateFlow}
    {code : List DisplayAlphabet} :
    SoundP8Report report ->
      List.Mem (P8ReportDatum.manuscriptCode M code) report.outputView ->
        exists R : GeneratedManuscriptRecognizer,
          SoundManuscriptFlow R M /\
            code = FlowEncoding M /\
            Decode code = some M := by
  intro hSound hMem
  have hReport :=
    hSound.right.left M code hMem
  cases hReport with
  | intro R hR =>
      cases hR with
      | intro hFlow hCode =>
          refine ⟨R, hFlow, ?_, ?_⟩
          · exact hCode
          · cases hCode
            exact manuscript_code_round_trip M

end BEDC.GroundCompiler.ChapterManuscript
