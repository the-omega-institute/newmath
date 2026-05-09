import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SourceChannel

namespace BEDC.GroundCompiler.ChapterFlow

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.SourceChannel

def ChapterCandidateFlow : Type :=
  EventFlow

def GeneratedChapterRecognizer : Type :=
  EventFlow

def DefinitionCandidateFlow : Type :=
  EventFlow

def GeneratedDefinitionRecognizer : Type :=
  EventFlow

def DefCand (S D : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow S) /\
    FormalCompilerInput (CompilerDatum.eventFlow D)

def RecognizesDefinition
    (R : GeneratedDefinitionRecognizer) (S D : DefinitionCandidateFlow) :
    Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    DefCand S D /\
    NonemptyEventFlow D

def DefinitionFlow
    (R : GeneratedDefinitionRecognizer) (S D : DefinitionCandidateFlow) :
    Prop :=
  RecognizesDefinition R S D

def DefinitionDependencySound
    (R : GeneratedDefinitionRecognizer) (S D : DefinitionCandidateFlow) :
    Prop :=
  DefinitionFlow R S D

def DefinitionCertificateSupported
    (R : GeneratedDefinitionRecognizer) (S D : DefinitionCandidateFlow) :
    Prop :=
  DefinitionFlow R S D /\ exists N : EventFlow, RecognizedNameCertFlow N

def DefinitionLedgerRecorded
    (_R : GeneratedDefinitionRecognizer) (S _D : DefinitionCandidateFlow) :
    Prop :=
  NonemptyEventFlow S

def DefinitionCandidateOnlyMarked
    (_R : GeneratedDefinitionRecognizer) (_S D : DefinitionCandidateFlow) :
    Prop :=
  NonemptyEventFlow D

def DefinitionNoHostNameInput : Prop :=
  Not (FormalCompilerInput CompilerDatum.hostObjectName)

def DefinitionSoundness
    (R : GeneratedDefinitionRecognizer) (S D : DefinitionCandidateFlow) :
    Prop :=
  DefinitionDependencySound R S D /\
    DefinitionCertificateSupported R S D /\
    DefinitionLedgerRecorded R S D /\
    DefinitionCandidateOnlyMarked R S D /\
    DefinitionNoHostNameInput

def SoundChapterDefinitionSubflow
    (R : GeneratedDefinitionRecognizer) (S D : DefinitionCandidateFlow) :
    Prop :=
  DefinitionFlow R S D /\ DefinitionSoundness R S D

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

inductive ChapterDependencyMarker : Type where
  | earlierGenerated
  | earlierRecognized
  | deferredObligation
  | cannotClaimItem
  | openObligation
  | futureBridge
  | unmarkedForward

def ChapterDependencyMarked (marker : ChapterDependencyMarker) : Prop :=
  Not (marker = ChapterDependencyMarker.unmarkedForward)

def ChapterDependencyOrder
    (R : GeneratedChapterRecognizer) (C dependencies _X : ChapterCandidateFlow)
    (marker : ChapterDependencyMarker) : Prop :=
  ChapDependencies R C dependencies /\ ChapterDependencyMarked marker

def ChapterOpenObligationRecorded
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists X : ChapterCandidateFlow,
    ChapCannotClaims R C X \/ ChapStatus R C X \/ ChapLedger R C X

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

def DependencySound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C1 : ChapterCandidateFlow, ChapDependencies R C C1

def DefinitionSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C2 : ChapterCandidateFlow, ChapDefinitions R C C2

def TheoremSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C4 : ChapterCandidateFlow, ChapTheorems R C C4

def ProofSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C5 : ChapterCandidateFlow, ChapProofs R C C5

def CertificateSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C6 : ChapterCandidateFlow, ChapCertificates R C C6

def LedgerSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C7 : ChapterCandidateFlow, ChapLedger R C C7

def CannotClaimSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C8 : ChapterCandidateFlow, ChapCannotClaims R C C8

def StatusSound
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  exists C9 : ChapterCandidateFlow, ChapStatus R C C9

def SoundRecognizedChapterFlow
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  CompleteChapterRecognition R C /\
    DependencySound R C /\
    DefinitionSound R C /\
    TheoremSound R C /\
    ProofSound R C /\
    CertificateSound R C /\
    LedgerSound R C /\
    CannotClaimSound R C /\
    StatusSound R C

def ChapterFlow (C : ChapterCandidateFlow) : Prop :=
  exists R : GeneratedChapterRecognizer, CompleteChapterRecognition R C

def ChapterCode (C : ChapterCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding C

def LegalChapterCode (c : List DisplayAlphabet) : Prop :=
  exists C : ChapterCandidateFlow, c = ChapterCode C

def RecognizesChapterCode
    (R : GeneratedChapterRecognizer) (c : List DisplayAlphabet) : Prop :=
  exists C : ChapterCandidateFlow, Decode c = some C /\ RecognizesChapter R C

inductive ChapterReadableViewFormat : Type where
  | markdown
  | latex
  | yaml
  | json
  | outline
  | theoremStatusTable
  | dependencyGraph

def HumanReadableChapterView
    (C : ChapterCandidateFlow) (_fmt : ChapterReadableViewFormat) : Prop :=
  ChapterFlow C

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

def ChapterClassifierRelation : Type :=
  ChapterCandidateFlow -> ChapterCandidateFlow -> Prop

def ChapterClassifierQuotient
    (rel : ChapterClassifierRelation) (C D : ChapterCandidateFlow) : Prop :=
  rel C D

def ClassifierCollapsesDistinctChapterCode
    (rel : ChapterClassifierRelation) : Prop :=
  exists C D : ChapterCandidateFlow,
    ChapterFlow C /\
      ChapterFlow D /\
      Not (ChapterCode C = ChapterCode D) /\
      ChapterClassifierQuotient rel C D

theorem classified_chapter_objects_not_code_bijective
    {rel : ChapterClassifierRelation} :
    (exists C D : ChapterCandidateFlow,
      ChapterFlow C /\
        ChapterFlow D /\
        Not (C = D) /\
        ChapterClassifierQuotient rel C D) ->
      ClassifierCollapsesDistinctChapterCode rel := by
  intro h
  cases h with
  | intro C hC =>
      cases hC with
      | intro D hD =>
          refine ⟨C, D, hD.left, hD.right.left, ?_, hD.right.right.right⟩
          intro hCode
          exact hD.right.right.left (chapter_code_injective hCode)

theorem chapter_flow_object_layer_differ {rel : ChapterClassifierRelation} :
    ClassifierCollapsesDistinctChapterCode rel ->
      exists C D : ChapterCandidateFlow,
        Not (ChapterCode C = ChapterCode D) /\
          ChapterClassifierQuotient rel C D := by
  intro hCollapse
  cases hCollapse with
  | intro C hC =>
      cases hC with
      | intro D hD =>
          exact ⟨C, D, hD.right.right.left, hD.right.right.right⟩

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

theorem no_chapter_recognition_by_channel_substring :
    (exists c u : List DisplayAlphabet,
      LegalZStream c /\
        ContiguousSubstring u c /\
        Not (OccursAsDecodedEvent u c)) /\
      (forall R : GeneratedChapterRecognizer,
        forall c : List DisplayAlphabet,
          RecognizesChapterCode R c ->
            exists C : ChapterCandidateFlow,
              Decode c = some C /\ RecognizesChapter R C) := by
  constructor
  · exact channel_substring_not_source_event
  · intro _ _ hCode
    exact hCode

theorem yaml_may_report {C : ChapterCandidateFlow} :
    ChapterFlow C ->
      HumanReadableChapterView C ChapterReadableViewFormat.yaml /\
        Not (FormalCompilerInput CompilerDatum.hostYAML) := by
  intro hChapter
  constructor
  · exact hChapter
  · exact structural_hidden_not_formal StructuralHiddenInput.hostYAML

theorem unsound_definition_blocks
    {R : GeneratedDefinitionRecognizer} {S D : DefinitionCandidateFlow} :
    Not (DefinitionSoundness R S D) ->
      Not (SoundChapterDefinitionSubflow R S D) := by
  intro hUnsound hSubflow
  exact hUnsound hSubflow.right

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

theorem sound_establishes_chapterhood
    {R : GeneratedChapterRecognizer} {C : ChapterCandidateFlow} :
    RecognizesChapter R C ->
      SoundRecognizedChapterFlow R C ->
      ChapterFlow C := by
  intro _ hSound
  exact ⟨R, hSound.left⟩

theorem chapter_yaml_input_hidden_structure :
    StructuralHiddenInput CompilerDatum.hostYAML /\
      Not (FormalCompilerInput CompilerDatum.hostYAML) := by
  constructor
  · exact StructuralHiddenInput.hostYAML
  · exact structural_hidden_not_formal StructuralHiddenInput.hostYAML

theorem chapter_yaml_output_not_input :
    Not (FormalCompilerInput CompilerDatum.hostYAML) :=
  structural_hidden_not_formal StructuralHiddenInput.hostYAML

theorem no_forward_dependency_without_marker
    {R : GeneratedChapterRecognizer} {C dependencies X : ChapterCandidateFlow} :
    Not
      (ChapterDependencyOrder R C dependencies X
        ChapterDependencyMarker.unmarkedForward) := by
  intro hOrder
  exact hOrder.right rfl

theorem open_obligations_recorded
    {R : GeneratedChapterRecognizer} {C : ChapterCandidateFlow} :
    CompleteChapterRecognition R C -> ChapterOpenObligationRecorded R C := by
  intro hComplete
  cases hComplete with
  | intro _ hSubflows =>
      cases hSubflows with
      | intro C0 hC0 =>
          cases hC0 with
          | intro C1 hC1 =>
              cases hC1 with
              | intro C2 hC2 =>
                  cases hC2 with
                  | intro C3 hC3 =>
                      cases hC3 with
                      | intro C4 hC4 =>
                          cases hC4 with
                          | intro C5 hC5 =>
                              cases hC5 with
                              | intro C6 hC6 =>
                                  cases hC6 with
                                  | intro C7 hC7 =>
                                      cases hC7 with
                                      | intro C8 hC8 =>
                                          cases hC8 with
                                          | intro C9 hC9 =>
                                              cases hC9 with
                                              | intro sigmaC hFields =>
                                                  cases hFields with
                                                  | intro _ hRest =>
                                                      cases hRest with
                                                      | intro _ hRest =>
                                                          cases hRest with
                                                          | intro _ hRest =>
                                                              cases hRest with
                                                              | intro _ hRest =>
                                                                  cases hRest with
                                                                  | intro _ hRest =>
                                                                      cases hRest with
                                                                      | intro _ hRest =>
                                                                          cases hRest with
                                                                          | intro _ hRest =>
                                                                              cases hRest with
                                                                              | intro _ hRest =>
                                                                                  cases hRest with
                                                                                  | intro hCannot _ =>
                                                                                      exact ⟨C8, Or.inl hCannot⟩

theorem chapter_seal_is_event_flow
    {R : GeneratedChapterRecognizer} {C sigmaC : ChapterCandidateFlow} :
    ChapSeal R C sigmaC ->
      FormalCompilerInput (CompilerDatum.eventFlow sigmaC) /\
        NonemptyEventFlow sigmaC := by
  intro hSeal
  exact hSeal.right

theorem chapter_flow_conservativity {C : ChapterCandidateFlow} {w : RawEvent}
    {m : DisplayAlphabet} :
    ChapterFlow C -> List.Mem w C -> List.Mem m w ->
      m = BEDC.FKernel.Mark.BMark.b0 \/ m = BEDC.FKernel.Mark.BMark.b1 := by
  intro _ _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

end BEDC.GroundCompiler.ChapterFlow
