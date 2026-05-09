import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.ChapterFlow

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def ChapterCandidateFlow : Type :=
  EventFlow

def GeneratedChapterRecognizer : Type :=
  EventFlow

def RecognizesChapter
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R C) /\
    NonemptyEventFlow C

def ChapterRole
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  RecognizesChapter R C /\
    FormalCompilerInput (CompilerDatum.eventFlow X) /\
    NonemptyEventFlow X

def ChapStart (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) :
    Prop :=
  ChapterRole R C X

def ChapDependencies
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapDefinitions
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapLemmas
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapTheorems
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapProofs
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapCertificates
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapLedger
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapCannotClaims
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapStatus
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapSeal
    (R : GeneratedChapterRecognizer) (C X : ChapterCandidateFlow) : Prop :=
  ChapterRole R C X

def ChapterSubflows
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 sigmaC : ChapterCandidateFlow,
    ChapStart R C C0 /\
    ChapDependencies R C C1 /\
    ChapDefinitions R C C2 /\
    ChapLemmas R C C3 /\
    ChapTheorems R C C4 /\
    ChapProofs R C C5 /\
    ChapCertificates R C C6 /\
    ChapLedger R C C7 /\
    ChapCannotClaims R C C8 /\
    ChapStatus R C C9 /\
    ChapSeal R C sigmaC

def CompleteChapterRecognition
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  RecognizesChapter R C /\ ChapterSubflows R C

def ChapterFlow (C : ChapterCandidateFlow) : Prop :=
  exists R : GeneratedChapterRecognizer, CompleteChapterRecognition R C

def ChapterCode (C : ChapterCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding C

def LegalChapterCode (c : List DisplayAlphabet) : Prop :=
  exists C : ChapterCandidateFlow, c = ChapterCode C

def RecognizesChapterCode
    (R : GeneratedChapterRecognizer) (c : List DisplayAlphabet) : Prop :=
  exists C : ChapterCandidateFlow, Decode c = some C /\ RecognizesChapter R C

theorem no_external_chapter_input :
    Not (FormalCompilerInput CompilerDatum.hostChapterPkg) :=
  structural_hidden_not_formal StructuralHiddenInput.hostChapterPkg

theorem chapter_recognition_preserves_code
    {R : GeneratedChapterRecognizer} {C : ChapterCandidateFlow} :
    RecognizesChapter R C -> ChapterCode C = FlowEncoding C := by
  intro _
  rfl

theorem chapter_code_not_new_code {C : ChapterCandidateFlow} :
    ChapterFlow C -> ChapterCode C = FlowEncoding C := by
  intro _
  rfl

theorem chapter_code_round_trip (C : ChapterCandidateFlow) :
    Decode (ChapterCode C) = some C :=
  flow_level_round_trip C

theorem chapter_code_injective {C D : ChapterCandidateFlow} :
    ChapterCode C = ChapterCode D -> C = D := by
  intro h
  have hDecode : Decode (ChapterCode C) = Decode (ChapterCode D) :=
    congrArg Decode h
  rw [chapter_code_round_trip C, chapter_code_round_trip D] at hDecode
  cases hDecode
  rfl

theorem chapter_code_bijective :
    (forall C : ChapterCandidateFlow, Decode (ChapterCode C) = some C) /\
      (forall c : List DisplayAlphabet,
        LegalChapterCode c ->
          exists C : ChapterCandidateFlow,
            Decode c = some C /\ ChapterCode C = c) := by
  constructor
  · intro C
    exact chapter_code_round_trip C
  · intro c h
    cases h with
    | intro C hC =>
        refine ⟨C, ?_, ?_⟩
        · rw [hC]
          exact chapter_code_round_trip C
        · exact hC.symm

theorem compile_decode_preserves_chapter_recognition
    {R : GeneratedChapterRecognizer} {C : ChapterCandidateFlow} :
    RecognizesChapter R C -> RecognizesChapterCode R (ChapterCode C) := by
  intro hRecognition
  exact ⟨C, chapter_code_round_trip C, hRecognition⟩

theorem chapter_recognition_invariant
    {R : GeneratedChapterRecognizer} {C : ChapterCandidateFlow} :
    RecognizesChapter R C ->
      exists D : ChapterCandidateFlow,
        Decode (ChapterCode C) = some D /\ RecognizesChapter R D := by
  intro hRecognition
  exact ⟨C, chapter_code_round_trip C, hRecognition⟩

theorem no_chapter_without_complete_recognition {C : ChapterCandidateFlow} :
    ChapterFlow C ->
      exists R : GeneratedChapterRecognizer, CompleteChapterRecognition R C := by
  intro hChapter
  exact hChapter

theorem incomplete_chapter_flow_not_chapter {C : ChapterCandidateFlow} :
    (forall R : GeneratedChapterRecognizer,
      Not (CompleteChapterRecognition R C)) ->
    Not (ChapterFlow C) := by
  intro hIncomplete hChapter
  cases hChapter with
  | intro R hComplete =>
      exact hIncomplete R hComplete

theorem title_alone_not_chapter
    {R : GeneratedChapterRecognizer} {C T : ChapterCandidateFlow} :
    ChapStart R C T ->
      (forall R' : GeneratedChapterRecognizer,
        Not (CompleteChapterRecognition R' C)) ->
      Not (ChapterFlow C) := by
  intro _ hIncomplete
  exact incomplete_chapter_flow_not_chapter hIncomplete

theorem theorem_list_alone_not_chapter
    {R : GeneratedChapterRecognizer} {C T : ChapterCandidateFlow} :
    ChapTheorems R C T ->
      (forall R' : GeneratedChapterRecognizer,
        Not (CompleteChapterRecognition R' C)) ->
      Not (ChapterFlow C) := by
  intro _ hIncomplete
  exact incomplete_chapter_flow_not_chapter hIncomplete

end BEDC.GroundCompiler.ChapterFlow
