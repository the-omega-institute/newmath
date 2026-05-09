import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.ChapterFlow
import BEDC.GroundCompiler.DerivCertGenerated
import BEDC.GroundCompiler.MetricsFlow
import BEDC.GroundCompiler.RecognizerFlows
import BEDC.GroundCompiler.SemanticMotif
import BEDC.GroundCompiler.SelfHostingCompilerFlow
import BEDC.GroundCompiler.SourceChannel
import BEDC.GroundCompiler.TheoremGenerated

namespace BEDC.GroundCompiler.MainTheorems

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.RecognizerFlows
open BEDC.GroundCompiler.SourceChannel

structure NoHiddenInputCompilerState where
  compile : EventFlow -> List DisplayAlphabet
  decode : List DisplayAlphabet -> Option EventFlow
  compile_legal : forall S : EventFlow, LegalZStream (compile S)
  decode_compile : forall S : EventFlow, decode (compile S) = some S
  legal_complete :
    forall c : List DisplayAlphabet,
      LegalZStream c ->
        exists S : EventFlow, decode c = some S /\ compile S = c
  hidden_excluded :
    forall d : CompilerDatum,
      StructuralHiddenInput d -> Not (FormalCompilerInput d)

def canonical_no_hidden_input_compiler_state : NoHiddenInputCompilerState where
  compile := FlowEncoding
  decode := Decode
  compile_legal := by
    intro S
    exact flow_encoding_legal_zstream S
  decode_compile := by
    intro S
    exact flow_level_round_trip S
  legal_complete := by
    intro c hLegal
    exact legal_stream_completeness hLegal
  hidden_excluded := by
    intro d hHidden
    exact structural_hidden_not_formal hHidden

def HiddenInput (d : CompilerDatum) : Prop :=
  StructuralHiddenInput d

theorem no_hidden_input
    (C : NoHiddenInputCompilerState) {d : CompilerDatum} :
    HiddenInput d -> Not (FormalCompilerInput d) := by
  intro hHidden
  exact C.hidden_excluded d hHidden

theorem channel_bijection :
    (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c ->
          exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c) := by
  exact channel_encoding_bijection

theorem channel_code_lossless {S T : EventFlow} :
    FlowEncoding S = FlowEncoding T -> S = T := by
  intro h
  have hS : Decode (FlowEncoding S) = some S := flow_level_round_trip S
  have hT : Decode (FlowEncoding T) = some T := flow_level_round_trip T
  rw [h] at hS
  have hSome : some S = some T := Eq.trans (Eq.symm hS) hT
  cases hSome
  rfl

theorem code_not_proof :
    exists c : List DisplayAlphabet,
      LegalZStream c /\
        Not (exists S : EventFlow,
          c = FlowEncoding S /\ RecognizedTheoremFlow S) := by
  exact legal_stream_not_theoremhood

theorem source_channel_separation :
    (forall S : EventFlow, LegalZStream (FlowEncoding S)) /\
      (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      Not (EventTerminator = EventEncoding [BMark.b1, BMark.b1]) /\
      exists c u : List DisplayAlphabet,
        LegalZStream c /\
          ContiguousSubstring u c /\
          Not (OccursAsDecodedEvent u c) := by
  exact layer_separation

theorem carry_not_channel_rewrite :
    LegalZStream (EventEncoding CarryPreNormal) /\
      Not (LegalZStream
        [BMark.b0, BMark.b1, BMark.b0, BMark.b1,
          BMark.b1, BMark.b0, BMark.b0]) := by
  exact no_channel_level_source_rewrite

def GeneratedStructure
    (RecognizesK : GeneratedRecognizer -> EventFlow -> Prop) : Prop :=
  exists R : GeneratedRecognizer, exists S : EventFlow,
    FormalCompilerInput (CompilerDatum.recognizedFlow R S) /\ RecognizesK R S

theorem structure_emergence :
    Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
      Not (FormalCompilerInput CompilerDatum.hostDerivCert) /\
      Not (FormalCompilerInput CompilerDatum.hostClosureCert) /\
      Not (FormalCompilerInput CompilerDatum.hostChapterPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
      Not (FormalCompilerInput CompilerDatum.hostManifest) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostNameCert
    · constructor
      · exact structural_hidden_not_formal StructuralHiddenInput.hostDerivCert
      · constructor
        · exact structural_hidden_not_formal StructuralHiddenInput.hostClosureCert
        · constructor
          · exact structural_hidden_not_formal StructuralHiddenInput.hostChapterPkg
          · constructor
            · exact
                structural_hidden_not_formal
                  StructuralHiddenInput.hostTheoremIdentifier
            · exact structural_hidden_not_formal StructuralHiddenInput.hostManifest

theorem yaml_ast_output_only :
    Not (FormalCompilerInput CompilerDatum.hostYAML) /\
      Not (FormalCompilerInput CompilerDatum.hostAST) /\
      Not (FormalCompilerInput CompilerDatum.hostManifest) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostYAML
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostAST
    · exact structural_hidden_not_formal StructuralHiddenInput.hostManifest

theorem recognizer_generatedness
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    FormalRecognitionEvidence R rho S ->
      CertifiedRecognizer R rho /\
        FormalCompilerInput (CompilerDatum.recognizedFlow R S) := by
  intro hEvidence
  exact ⟨hEvidence.left, hEvidence.right⟩

theorem recognizer_generatedness_theorem
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    FormalRecognitionEvidence R rho S ->
      CertifiedRecognizer R rho /\
        FormalCompilerInput (CompilerDatum.recognizedFlow R S) := by
  intro hEvidence
  exact recognizer_generatedness hEvidence

def SelfHostedCompiler
    (behavior :
      BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerBehaviorRelation)
    (C : BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerCandidateFlow) :
    Prop :=
  BEDC.GroundCompiler.SelfHostingCompilerFlow.SelfHostingCompilerFlow behavior C

theorem self_hosting_removes_hidden_compiler
    {behavior :
      BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerBehaviorRelation}
    {C : BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerCandidateFlow} :
    SelfHostedCompiler behavior C ->
      BEDC.GroundCompiler.SelfHostingCompilerFlow.RecognizerHierarchyCoversCompilerTower C ->
        BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerNoLongerHiddenInput
          behavior C := by
  intro hSelf hHierarchy
  exact
    BEDC.GroundCompiler.SelfHostingCompilerFlow.self_hosting_removes_hidden_input
      hSelf hHierarchy

def CertificateMediatedExport (N s : EventFlow) : Prop :=
  DerivCertGenerated.AcceptGateFlow N s

def AcceptedExport (N s : EventFlow) : Prop :=
  CertificateMediatedExport N s

theorem accepted_export (N s : EventFlow) :
    AcceptedExport N s ↔ DerivCertGenerated.AcceptGateFlow N s := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem code_existence_not_export (N s : EventFlow) :
    exists c : List DisplayAlphabet,
      LegalZStream c /\
        Not (DerivCertGenerated.RecognizesAcceptanceCode c N s) := by
  exact ⟨[], DerivCertGenerated.code_existence_not_acceptance N s⟩

theorem motif_existence_not_export :
    Not (forall Rfam : SemanticMotif.GeneratedMotifRecognizer -> Prop,
      forall S mu M L : EventFlow,
        SemanticMotif.MotifProfile Rfam S mu M L -> AcceptedObjectFlow S) := by
  exact SemanticMotif.motif_analysis_cannot_license_mature_objects

def CanonicalTheoremFlow (T : EventFlow) : Prop :=
  exists R : TheoremGenerated.GeneratedTheoremRecognizer,
    TheoremGenerated.SoundTheoremFlow R T /\
      TheoremGenerated.SiteSoundTheoremRecognition R T

def TheoremCode (T : EventFlow) : List DisplayAlphabet :=
  FlowEncoding T

def LegalCanonicalTheoremCode (c : List DisplayAlphabet) : Prop :=
  exists T : EventFlow, CanonicalTheoremFlow T /\ c = TheoremCode T

theorem theorem_code_bijection :
    (forall T : EventFlow,
      CanonicalTheoremFlow T -> LegalCanonicalTheoremCode (TheoremCode T)) /\
      (forall T U : EventFlow,
        CanonicalTheoremFlow T ->
          CanonicalTheoremFlow U -> TheoremCode T = TheoremCode U -> T = U) /\
      (forall c : List DisplayAlphabet,
        LegalCanonicalTheoremCode c ->
          exists T : EventFlow,
            CanonicalTheoremFlow T /\ Decode c = some T /\ TheoremCode T = c) := by
  constructor
  · intro T hCanonical
    exact ⟨T, hCanonical, rfl⟩
  · constructor
    · intro T U _ _ hCode
      exact channel_code_lossless hCode
    · intro c hLegal
      cases hLegal with
      | intro T hT =>
          refine ⟨T, hT.left, ?_, hT.right.symm⟩
          rw [hT.right]
          exact flow_level_round_trip T

theorem proposition_not_theorem_code :
    exists R : TheoremGenerated.GeneratedTheoremRecognizer,
      exists statement T U : TheoremGenerated.TheoremCandidateFlow,
        Not (T = U) /\
          TheoremGenerated.TheoremRoleSubflow R T statement
            TheoremGenerated.TheoremRole.statement /\
          TheoremGenerated.TheoremRoleSubflow R U statement
            TheoremGenerated.TheoremRole.statement := by
  exact TheoremGenerated.same_statement_multiple_flows

theorem theorem_code_not_proof :
    exists c : List DisplayAlphabet,
      TheoremGenerated.LegalTheoremCode c /\
        exists T : TheoremGenerated.TheoremCandidateFlow,
          Decode c = some T /\
            (forall R : TheoremGenerated.GeneratedTheoremRecognizer,
              Not (TheoremGenerated.ProofSoundTheoremRecognition R T)) := by
  exact TheoremGenerated.theorem_code_is_not_proof

def CanonicalChapterFlow (C : EventFlow) : Prop :=
  exists R : ChapterFlow.GeneratedChapterRecognizer,
    ChapterFlow.SoundRecognizedChapterFlow R C

def ChapterCode (C : EventFlow) : List DisplayAlphabet :=
  ChapterFlow.ChapterCode C

def LegalCanonicalChapterCode (c : List DisplayAlphabet) : Prop :=
  exists C : EventFlow, CanonicalChapterFlow C /\ c = ChapterCode C

theorem chapter_code_bijection :
    (forall C : EventFlow,
      CanonicalChapterFlow C -> LegalCanonicalChapterCode (ChapterCode C)) /\
      (forall C D : EventFlow,
        CanonicalChapterFlow C ->
          CanonicalChapterFlow D -> ChapterCode C = ChapterCode D -> C = D) /\
      (forall c : List DisplayAlphabet,
        LegalCanonicalChapterCode c ->
          exists C : EventFlow,
            CanonicalChapterFlow C /\ Decode c = some C /\ ChapterCode C = c) := by
  constructor
  · intro C hCanonical
    exact ⟨C, hCanonical, rfl⟩
  · constructor
    · intro C D _ _ hCode
      exact ChapterFlow.chapter_code_injective hCode
    · intro c hLegal
      cases hLegal with
      | intro C hC =>
          refine ⟨C, hC.left, ?_, hC.right.symm⟩
          rw [hC.right]
          exact ChapterFlow.chapter_code_round_trip C

inductive ChapterTopic : Type where
  | compilerArchitecture

def ChapterTopicOf (_C : EventFlow) : ChapterTopic :=
  ChapterTopic.compilerArchitecture

theorem topic_not_chapter_code :
    exists C D : EventFlow,
      Not (C = D) /\
        ChapterTopicOf C = ChapterTopicOf D /\
        Not (ChapterCode C = ChapterCode D) := by
  refine ⟨[], [[BMark.b0]], ?_⟩
  constructor
  · intro h
    cases h
  · constructor
    · rfl
    · intro hCode
      simp [ChapterCode, ChapterFlow.ChapterCode, FlowEncoding,
        EventEncoding, BodyEncoding, EventTerminator] at hCode

def RawFlowCodeLayer (S : EventFlow) (c : List DisplayAlphabet) : Prop :=
  c = FlowEncoding S

def ClassifiedObjectLayer
    (classifier : EventFlow -> EventFlow -> Prop) (S T : EventFlow) : Prop :=
  classifier S T

def ErasureClassifier (S T : EventFlow) : Prop :=
  erase S = erase T

theorem classifier_quotient_many_to_one :
    exists S T : EventFlow,
      Not (S = T) /\ ClassifiedObjectLayer ErasureClassifier S T := by
  refine
    ⟨[[BMark.b0], [BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b0]],
      [[BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b0, BMark.b0]],
      ?_⟩
  constructor
  · intro h
    cases h
  · rfl

theorem normal_address_requires_ledger (w v : RawEvent) :
    Not (SourceCarryLedger w v = [v]) := by
  exact normal_address_does_not_erase_raw_event w v

theorem declared_bootstrap_boundary
    {C : BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerCandidateFlow} :
    BEDC.GroundCompiler.SelfHostingCompilerFlow.RemainingBootstrapBoundary C ->
      BEDC.GroundCompiler.SelfHostingCompilerFlow.BootstrapRecorded C := by
  exact
    BEDC.GroundCompiler.SelfHostingCompilerFlow.remaining_bootstrap_boundary_visible

theorem motif_analysis
    {R : SemanticMotif.GeneratedMotifRecognizer} {S M : EventFlow}
    {mu : SemanticMotif.MotifRole} :
    SemanticMotif.MotifOccurrence R S M mu ->
      FormalCompilerInput (CompilerDatum.eventFlow R) /\
        exists L : EventFlow, SemanticMotif.MotifLedger R S M mu L := by
  intro h
  exact ⟨h.left, SemanticMotif.no_motif_without_ledger h⟩

theorem metric_conservativity :
    (forall report : MetricsFlow.MetricReport,
      forall S : EventFlow,
      forall w : RawEvent,
      forall m : DisplayAlphabet,
        List.Mem S report.sourceFlows ->
          List.Mem w S ->
            List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) /\
      exists report : MetricsFlow.MetricReport, exists S : EventFlow,
        List.Mem S report.sourceFlows /\ Not (AcceptedObjectFlow S) := by
  constructor
  · intro report S w m hS hw hm
    exact MetricsFlow.metrics_conservativity hS hw hm
  · exact MetricsFlow.metrics_cannot_replace_certificates

theorem similarity_not_identity :
    exists Rfam : SemanticMotif.GeneratedMotifRecognizer -> Prop,
      exists S T mu M L : EventFlow,
        SemanticMotif.MotifOverlap Rfam S T mu M L /\ Not (S = T) := by
  exact SemanticMotif.motif_similarity_not_object_equality

inductive CannotClaimKind : Type where
  | arbitraryBinaryMeaning
  | channelSubstringSourceEvent
  | sourceCarryChannelRewrite
  | codeImpliesProof
  | codeImpliesAcceptedObject
  | structuresAreInputs
  | recognizerIsHostParser
  | classifierQuotientPreservesRawBijection
  | motifSimilarityImpliesObjectEquality
  | carryMotifImpliesDimension
  | sealMotifImpliesCompletion
  | reportIsProof
  | selfHostingImpliesRawEquality
  | fullNoHiddenInputWithoutSelfHosting
deriving DecidableEq

structure CompilerCannotClaimEntry where
  claimText : EventFlow
  status : EventFlow
  whyNotDischarged : EventFlow
  requiredUpgrade : EventFlow
  ledger : EventFlow

inductive RequiredCannotClaimEntries : CannotClaimKind -> Prop where
  | arbitraryBinaryMeaning :
      RequiredCannotClaimEntries CannotClaimKind.arbitraryBinaryMeaning
  | channelSubstringSourceEvent :
      RequiredCannotClaimEntries CannotClaimKind.channelSubstringSourceEvent
  | sourceCarryChannelRewrite :
      RequiredCannotClaimEntries CannotClaimKind.sourceCarryChannelRewrite
  | codeImpliesProof :
      RequiredCannotClaimEntries CannotClaimKind.codeImpliesProof
  | codeImpliesAcceptedObject :
      RequiredCannotClaimEntries CannotClaimKind.codeImpliesAcceptedObject
  | structuresAreInputs :
      RequiredCannotClaimEntries CannotClaimKind.structuresAreInputs
  | recognizerIsHostParser :
      RequiredCannotClaimEntries CannotClaimKind.recognizerIsHostParser
  | classifierQuotientPreservesRawBijection :
      RequiredCannotClaimEntries
        CannotClaimKind.classifierQuotientPreservesRawBijection
  | motifSimilarityImpliesObjectEquality :
      RequiredCannotClaimEntries
        CannotClaimKind.motifSimilarityImpliesObjectEquality
  | carryMotifImpliesDimension :
      RequiredCannotClaimEntries CannotClaimKind.carryMotifImpliesDimension
  | sealMotifImpliesCompletion :
      RequiredCannotClaimEntries CannotClaimKind.sealMotifImpliesCompletion
  | reportIsProof :
      RequiredCannotClaimEntries CannotClaimKind.reportIsProof
  | selfHostingImpliesRawEquality :
      RequiredCannotClaimEntries CannotClaimKind.selfHostingImpliesRawEquality
  | fullNoHiddenInputWithoutSelfHosting :
      RequiredCannotClaimEntries
        CannotClaimKind.fullNoHiddenInputWithoutSelfHosting

def RegistryEntry
    (registry : List (CannotClaimKind × CompilerCannotClaimEntry))
    (kind : CannotClaimKind) (entry : CompilerCannotClaimEntry) : Prop :=
  List.Mem (kind, entry) registry

def RegistryHasLedger
    (registry : List (CannotClaimKind × CompilerCannotClaimEntry))
    (kind : CannotClaimKind) : Prop :=
  exists entry : CompilerCannotClaimEntry,
    RegistryEntry registry kind entry /\ NonemptyEventFlow entry.ledger

def CannotClaimRegistryAdequate
    (registry : List (CannotClaimKind × CompilerCannotClaimEntry)) : Prop :=
  forall kind : CannotClaimKind,
    RequiredCannotClaimEntries kind -> RegistryHasLedger registry kind

theorem cannot_claim_registry_mandatory
    {registry : List (CannotClaimKind × CompilerCannotClaimEntry)} :
    CannotClaimRegistryAdequate registry ->
      RegistryHasLedger registry CannotClaimKind.arbitraryBinaryMeaning /\
      RegistryHasLedger registry CannotClaimKind.channelSubstringSourceEvent /\
      RegistryHasLedger registry CannotClaimKind.sourceCarryChannelRewrite /\
      RegistryHasLedger registry CannotClaimKind.codeImpliesProof /\
      RegistryHasLedger registry CannotClaimKind.codeImpliesAcceptedObject /\
      RegistryHasLedger registry CannotClaimKind.structuresAreInputs /\
      RegistryHasLedger registry CannotClaimKind.recognizerIsHostParser /\
      RegistryHasLedger registry
        CannotClaimKind.classifierQuotientPreservesRawBijection /\
      RegistryHasLedger registry
        CannotClaimKind.motifSimilarityImpliesObjectEquality /\
      RegistryHasLedger registry CannotClaimKind.carryMotifImpliesDimension /\
      RegistryHasLedger registry CannotClaimKind.sealMotifImpliesCompletion /\
      RegistryHasLedger registry CannotClaimKind.reportIsProof /\
      RegistryHasLedger registry CannotClaimKind.selfHostingImpliesRawEquality /\
      RegistryHasLedger registry
        CannotClaimKind.fullNoHiddenInputWithoutSelfHosting := by
  intro h
  constructor
  · exact h CannotClaimKind.arbitraryBinaryMeaning
      RequiredCannotClaimEntries.arbitraryBinaryMeaning
  · constructor
    · exact h CannotClaimKind.channelSubstringSourceEvent
        RequiredCannotClaimEntries.channelSubstringSourceEvent
    · constructor
      · exact h CannotClaimKind.sourceCarryChannelRewrite
          RequiredCannotClaimEntries.sourceCarryChannelRewrite
      · constructor
        · exact h CannotClaimKind.codeImpliesProof
            RequiredCannotClaimEntries.codeImpliesProof
        · constructor
          · exact h CannotClaimKind.codeImpliesAcceptedObject
              RequiredCannotClaimEntries.codeImpliesAcceptedObject
          · constructor
            · exact h CannotClaimKind.structuresAreInputs
                RequiredCannotClaimEntries.structuresAreInputs
            · constructor
              · exact h CannotClaimKind.recognizerIsHostParser
                  RequiredCannotClaimEntries.recognizerIsHostParser
              · constructor
                · exact h
                    CannotClaimKind.classifierQuotientPreservesRawBijection
                    RequiredCannotClaimEntries.classifierQuotientPreservesRawBijection
                · constructor
                  · exact h CannotClaimKind.motifSimilarityImpliesObjectEquality
                      RequiredCannotClaimEntries.motifSimilarityImpliesObjectEquality
                  · constructor
                    · exact h CannotClaimKind.carryMotifImpliesDimension
                        RequiredCannotClaimEntries.carryMotifImpliesDimension
                    · constructor
                      · exact h CannotClaimKind.sealMotifImpliesCompletion
                          RequiredCannotClaimEntries.sealMotifImpliesCompletion
                      · constructor
                        · exact h CannotClaimKind.reportIsProof
                            RequiredCannotClaimEntries.reportIsProof
                        · constructor
                          · exact h CannotClaimKind.selfHostingImpliesRawEquality
                              RequiredCannotClaimEntries.selfHostingImpliesRawEquality
                          · exact h
                              CannotClaimKind.fullNoHiddenInputWithoutSelfHosting
                              RequiredCannotClaimEntries.fullNoHiddenInputWithoutSelfHosting

def GlobalConservativityStatement : Prop :=
    (forall S : EventFlow,
      forall w : RawEvent,
      forall m : DisplayAlphabet,
        List.Mem w S -> List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) /\
      (forall S : EventFlow, LegalZStream (FlowEncoding S)) /\
      (forall d : CompilerDatum,
        StructuralHiddenInput d -> Not (FormalCompilerInput d)) /\
      (forall report : MetricsFlow.MetricReport,
        forall S : EventFlow,
        forall w : RawEvent,
        forall m : DisplayAlphabet,
          List.Mem S report.sourceFlows ->
            List.Mem w S ->
              List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) /\
      Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
      Not (FormalCompilerInput CompilerDatum.hostDerivCert) /\
      Not (FormalCompilerInput CompilerDatum.hostClosureCert)

theorem global_conservativity :
    GlobalConservativityStatement := by
  constructor
  · intro S w m hw hm
    exact event_flow_conservativity hw hm
  · constructor
    · intro S
      exact flow_encoding_legal_zstream S
    · constructor
      · intro d hHidden
        exact structural_hidden_not_formal hHidden
      · constructor
        · intro report S w m hS hw hm
          exact MetricsFlow.metrics_conservativity hS hw hm
        · constructor
          · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
          · constructor
            · exact
                structural_hidden_not_formal StructuralHiddenInput.hostNameCert
            · constructor
              · exact
                  structural_hidden_not_formal
                    StructuralHiddenInput.hostDerivCert
              · exact
                  structural_hidden_not_formal
                    StructuralHiddenInput.hostClosureCert

def CompilerLayerAddressAnalysisStatement : Prop :=
    (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c ->
          exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c) /\
      (exists c : List DisplayAlphabet,
        LegalZStream c /\
          Not (exists S : EventFlow,
            c = FlowEncoding S /\ RecognizedTheoremFlow S)) /\
      (exists report : MetricsFlow.MetricReport, exists S : EventFlow,
        List.Mem S report.sourceFlows /\ Not (AcceptedObjectFlow S)) /\
      GlobalConservativityStatement

theorem compiler_layer_address_analysis_layer :
    CompilerLayerAddressAnalysisStatement := by
  constructor
  · exact flow_level_round_trip
  · constructor
    · intro c hLegal
      exact legal_stream_completeness hLegal
    · constructor
      · exact code_not_proof
      · constructor
        · exact metric_conservativity.right
        · exact global_conservativity

def NoHiddenInputStreamingCompilerStatement : Prop :=
    (forall S : EventFlow,
      FormalCompilerInput (CompilerDatum.eventFlow S) /\
        LegalZStream (FlowEncoding S) /\
        Decode (FlowEncoding S) = some S) /\
      ((forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
        (forall c : List DisplayAlphabet,
          LegalZStream c ->
            exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c)) /\
      (Not (FormalCompilerInput CompilerDatum.hostPkg) /\
        Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
        Not (FormalCompilerInput CompilerDatum.hostDerivCert) /\
        Not (FormalCompilerInput CompilerDatum.hostClosureCert) /\
        Not (FormalCompilerInput CompilerDatum.hostChapterPkg) /\
        Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
        Not (FormalCompilerInput CompilerDatum.hostManifest)) /\
      (forall R : RecognizerCandidateFlow,
        forall rho : RecognitionRole,
        forall S : EventFlow,
          FormalRecognitionEvidence R rho S ->
            CertifiedRecognizer R rho /\
              FormalCompilerInput (CompilerDatum.recognizedFlow R S)) /\
      (forall N s : EventFlow,
        AcceptedExport N s ↔ DerivCertGenerated.AcceptGateFlow N s) /\
      ((forall T : EventFlow,
        CanonicalTheoremFlow T -> LegalCanonicalTheoremCode (TheoremCode T)) /\
        (forall T U : EventFlow,
          CanonicalTheoremFlow T ->
            CanonicalTheoremFlow U -> TheoremCode T = TheoremCode U -> T = U) /\
        (forall c : List DisplayAlphabet,
          LegalCanonicalTheoremCode c ->
            exists T : EventFlow,
              CanonicalTheoremFlow T /\
                Decode c = some T /\ TheoremCode T = c)) /\
      ((forall C : EventFlow,
        CanonicalChapterFlow C -> LegalCanonicalChapterCode (ChapterCode C)) /\
        (forall C D : EventFlow,
          CanonicalChapterFlow C ->
            CanonicalChapterFlow D -> ChapterCode C = ChapterCode D -> C = D) /\
        (forall c : List DisplayAlphabet,
          LegalCanonicalChapterCode c ->
            exists C : EventFlow,
              CanonicalChapterFlow C /\
                Decode c = some C /\ ChapterCode C = c)) /\
      (exists S T : EventFlow,
        Not (S = T) /\ ClassifiedObjectLayer ErasureClassifier S T) /\
      ((forall S : EventFlow, LegalZStream (FlowEncoding S)) /\
        (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
        Not (EventTerminator = EventEncoding [BMark.b1, BMark.b1]) /\
        exists c u : List DisplayAlphabet,
          LegalZStream c /\
            ContiguousSubstring u c /\ Not (OccursAsDecodedEvent u c)) /\
      ((forall report : MetricsFlow.MetricReport,
        forall S : EventFlow,
        forall w : RawEvent,
        forall m : DisplayAlphabet,
          List.Mem S report.sourceFlows ->
            List.Mem w S ->
              List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) /\
        exists report : MetricsFlow.MetricReport, exists S : EventFlow,
          List.Mem S report.sourceFlows /\ Not (AcceptedObjectFlow S)) /\
      (forall behavior :
        BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerBehaviorRelation,
        forall C :
          BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerCandidateFlow,
          SelfHostedCompiler behavior C ->
            BEDC.GroundCompiler.SelfHostingCompilerFlow.RecognizerHierarchyCoversCompilerTower C ->
              BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerNoLongerHiddenInput
                behavior C) /\
      (forall C :
        BEDC.GroundCompiler.SelfHostingCompilerFlow.CompilerCandidateFlow,
        BEDC.GroundCompiler.SelfHostingCompilerFlow.RemainingBootstrapBoundary C ->
          BEDC.GroundCompiler.SelfHostingCompilerFlow.BootstrapRecorded C) /\
      GlobalConservativityStatement

theorem no_hidden_input_streaming_compiler :
    NoHiddenInputStreamingCompilerStatement := by
  constructor
  · intro S
    constructor
    · exact FormalCompilerInput.eventFlow S
    · constructor
      · exact flow_encoding_legal_zstream S
      · exact flow_level_round_trip S
  · constructor
    · exact channel_bijection
    · constructor
      · exact structure_emergence
      · constructor
        · intro R rho S hEvidence
          exact recognizer_generatedness hEvidence
        · constructor
          · intro N s
            exact accepted_export N s
          · constructor
            · exact theorem_code_bijection
            · constructor
              · exact chapter_code_bijection
              · constructor
                · exact classifier_quotient_many_to_one
                · constructor
                  · exact source_channel_separation
                  · constructor
                    · exact metric_conservativity
                    · constructor
                      · intro behavior C hSelf hHierarchy
                        exact
                          self_hosting_removes_hidden_compiler hSelf
                            hHierarchy
                      · constructor
                        · intro C hBoundary
                          exact declared_bootstrap_boundary hBoundary
                        · exact global_conservativity

end BEDC.GroundCompiler.MainTheorems
