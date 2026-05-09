import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.TheoremGenerated

namespace BEDC.GroundCompiler.SelfHostingCompilerFlow

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.TheoremGenerated

def CompilerCandidateFlow : Type := EventFlow

def CompilerRecognitionRelation
    (R C : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R C)

def CompilerBehaviorRelation : Type :=
  CompilerCandidateFlow -> EventFlow -> EventFlow -> Prop

def CompilerTaskDomain (C D : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow C D)

def CompilerTargetDomain (C T : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow C T)

def CompilerCertificateCandidateFlow : Type := EventFlow

def CompilerCertificateRecognition
    (RK : EventFlow) (KC : CompilerCertificateCandidateFlow)
    (C : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow RK KC) /\
    FormalCompilerInput (CompilerDatum.eventFlow C)

def P9Subflow (S C : EventFlow) : Prop :=
  exists pre : EventFlow, exists post : EventFlow,
    S = List.append (List.append pre C) post

inductive CompilerCertificateRole : Type where
  | inputDomain
  | outputDomain
  | encodingRule
  | decodingRule
  | roundTrip
  | recognizerHierarchy
  | ledger
  | failure
  | kernelConservativity
  | selfDescription
  | closingSeal

def CompilerCertificateFieldSubflow
    (RK : EventFlow) (KC part : EventFlow)
    (_role : CompilerCertificateRole) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow RK KC) /\
    P9Subflow KC part

def CompilerCertificateFields
    (RK : EventFlow) (KC : CompilerCertificateCandidateFlow)
    (C : CompilerCandidateFlow) : Prop :=
  CompilerCertificateRecognition RK KC C /\
    exists inputDomain outputDomain encoding decoding roundTrip hierarchy
      ledger failure kernel selfDescription closingSeal : EventFlow,
      CompilerCertificateFieldSubflow RK KC inputDomain
        CompilerCertificateRole.inputDomain /\
      CompilerCertificateFieldSubflow RK KC outputDomain
        CompilerCertificateRole.outputDomain /\
      CompilerCertificateFieldSubflow RK KC encoding
        CompilerCertificateRole.encodingRule /\
      CompilerCertificateFieldSubflow RK KC decoding
        CompilerCertificateRole.decodingRule /\
      CompilerCertificateFieldSubflow RK KC roundTrip
        CompilerCertificateRole.roundTrip /\
      CompilerCertificateFieldSubflow RK KC hierarchy
        CompilerCertificateRole.recognizerHierarchy /\
      CompilerCertificateFieldSubflow RK KC ledger
        CompilerCertificateRole.ledger /\
      CompilerCertificateFieldSubflow RK KC failure
        CompilerCertificateRole.failure /\
      CompilerCertificateFieldSubflow RK KC kernel
        CompilerCertificateRole.kernelConservativity /\
      CompilerCertificateFieldSubflow RK KC selfDescription
        CompilerCertificateRole.selfDescription /\
      CompilerCertificateFieldSubflow RK KC closingSeal
        CompilerCertificateRole.closingSeal

def CertifiedCompiler (C : CompilerCandidateFlow) : Prop :=
  exists KC : CompilerCertificateCandidateFlow,
    exists RK : EventFlow, CompilerCertificateRecognition RK KC C

def FormalCompilationJudgment
    (Compiles : CompilerBehaviorRelation)
    (C : CompilerCandidateFlow) (S T : EventFlow) : Prop :=
  CertifiedCompiler C /\ Compiles C S T

theorem formal_compilation_requires_certificate
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    FormalCompilationJudgment Compiles C S T -> CertifiedCompiler C := by
  intro hJudgment
  exact hJudgment.left

theorem uncertified_cannot_compile
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    Not (CertifiedCompiler C) ->
      Not (FormalCompilationJudgment Compiles C S T) := by
  intro hUncertified hJudgment
  exact hUncertified hJudgment.left

theorem host_output_inadmissible_without_certificate
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    Not (CertifiedCompiler C) ->
      Not (FormalCompilationJudgment Compiles C S T) := by
  exact uncertified_cannot_compile

inductive BootstrapRole : Type where
  | channelEncoderDecoder
  | eventFlowRecognizer
  | recognizerCertificateChecker

def BootstrapCompiler
    (C : CompilerCandidateFlow) (_rho : BootstrapRole) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow C)

def BootstrapObligation
    (B : EventFlow) (C : CompilerCandidateFlow) (rho : BootstrapRole) : Prop :=
  NonemptyEventFlow B /\ P9Subflow B C /\ BootstrapCompiler C rho

def BootstrapRecorded (C : CompilerCandidateFlow) : Prop :=
  exists B : EventFlow, exists rho : BootstrapRole, BootstrapObligation B C rho

def BoundaryCompilationJudgment
    (Compiles : CompilerBehaviorRelation)
    (C : CompilerCandidateFlow) (S T : EventFlow) : Prop :=
  (CertifiedCompiler C \/ BootstrapRecorded C) /\ Compiles C S T

theorem bootstrap_must_be_explicit
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    BoundaryCompilationJudgment Compiles C S T ->
      CertifiedCompiler C \/ BootstrapRecorded C := by
  intro hJudgment
  exact hJudgment.left

def HiddenBootstrapUse
    (Compiles : CompilerBehaviorRelation)
    (C : CompilerCandidateFlow) (S T : EventFlow) : Prop :=
  Compiles C S T /\ Not (CertifiedCompiler C) /\ Not (BootstrapRecorded C)

def NoHiddenCompilerUse
    (Compiles : CompilerBehaviorRelation)
    (C : CompilerCandidateFlow) (S T : EventFlow) : Prop :=
  Compiles C S T -> CertifiedCompiler C \/ BootstrapRecorded C

theorem hidden_bootstrap_violates
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    HiddenBootstrapUse Compiles C S T ->
      Not (NoHiddenCompilerUse Compiles C S T) := by
  intro hHidden hNoHidden
  have hBoundary : CertifiedCompiler C \/ BootstrapRecorded C :=
    hNoHidden hHidden.left
  cases hBoundary with
  | inl hCertified =>
      exact hHidden.right.left hCertified
  | inr hBootstrap =>
      exact hHidden.right.right hBootstrap

def CompilerBehaviorClassifier
    (behavior : CompilerBehaviorRelation)
    (C' C : CompilerCandidateFlow) : Prop :=
  CertifiedCompiler C /\
    CertifiedCompiler C' /\
    (forall S T : EventFlow, behavior C S T -> behavior C' S T) /\
    (forall S T : EventFlow, behavior C' S T -> behavior C S T)

def SelfCompiles
    (behavior : CompilerBehaviorRelation) (C : CompilerCandidateFlow) : Prop :=
  exists C' : CompilerCandidateFlow,
    behavior C C C' /\ CompilerBehaviorClassifier behavior C' C

def SelfHostingCompilerFlow
    (behavior : CompilerBehaviorRelation) (C : CompilerCandidateFlow) : Prop :=
  CertifiedCompiler C /\
    (exists RC : EventFlow, CompilerRecognitionRelation RC C) /\
    exists C' L : EventFlow,
      behavior C C C' /\
        CompilerBehaviorClassifier behavior C' C /\
        NonemptyEventFlow L

def SelfHostingLedger (_C : CompilerCandidateFlow) (L : EventFlow) : Prop :=
  NonemptyEventFlow L

theorem self_hosting_yields_behavior_classifier
    {behavior : CompilerBehaviorRelation} {C : CompilerCandidateFlow} :
    SelfHostingCompilerFlow behavior C ->
      exists C' : CompilerCandidateFlow,
        CompilerBehaviorClassifier behavior C' C := by
  intro hSelf
  cases hSelf.right.right with
  | intro C' hC' =>
      cases hC' with
      | intro _L hLedger =>
          exact ⟨C', hLedger.right.left⟩

theorem self_hosting_not_kernel_equality
    {behavior : CompilerBehaviorRelation} {C : CompilerCandidateFlow} :
    SelfHostingCompilerFlow behavior C ->
      exists C' : CompilerCandidateFlow, exists L : EventFlow,
        behavior C C C' /\
          CompilerBehaviorClassifier behavior C' C /\
          SelfHostingLedger C L := by
  intro hSelf
  cases hSelf.right.right with
  | intro C' hC' =>
      cases hC' with
      | intro L hLedger =>
          exact ⟨C', L, hLedger.left, hLedger.right.left, hLedger.right.right⟩

theorem self_hosting_requires_ledger
    {behavior : CompilerBehaviorRelation} {C : CompilerCandidateFlow} :
    SelfHostingCompilerFlow behavior C ->
      exists L : EventFlow, SelfHostingLedger C L := by
  intro hSelf
  cases hSelf.right.right with
  | intro _C' hC' =>
      cases hC' with
      | intro L hLedger =>
          exact ⟨L, hLedger.right.right⟩

def RecognizerHierarchyCoversCompilerTower
    (C : CompilerCandidateFlow) : Prop :=
  exists package nameCert derivCert theoremFlow chapter compiler : EventFlow,
    FormalCompilerInput (CompilerDatum.recognizedFlow C package) /\
      FormalCompilerInput (CompilerDatum.recognizedFlow C nameCert) /\
      FormalCompilerInput (CompilerDatum.recognizedFlow C derivCert) /\
      FormalCompilerInput (CompilerDatum.recognizedFlow C theoremFlow) /\
      FormalCompilerInput (CompilerDatum.recognizedFlow C chapter) /\
      FormalCompilerInput (CompilerDatum.recognizedFlow C compiler)

def CompilerNoLongerHiddenInput
    (behavior : CompilerBehaviorRelation) (C : CompilerCandidateFlow) :
    Prop :=
  SelfHostingCompilerFlow behavior C /\
    RecognizerHierarchyCoversCompilerTower C /\
    exists L : EventFlow, SelfHostingLedger C L

theorem self_hosting_removes_hidden_input
    {behavior : CompilerBehaviorRelation} {C : CompilerCandidateFlow} :
    SelfHostingCompilerFlow behavior C ->
      RecognizerHierarchyCoversCompilerTower C ->
        CompilerNoLongerHiddenInput behavior C := by
  intro hSelf hHierarchy
  exact ⟨hSelf, hHierarchy, self_hosting_requires_ledger hSelf⟩

theorem full_claim_requires_boundary
    {behavior : CompilerBehaviorRelation} {C : CompilerCandidateFlow} :
    Not (SelfHostingCompilerFlow behavior C) ->
      (SelfHostingCompilerFlow behavior C \/ BootstrapRecorded C) ->
        BootstrapRecorded C := by
  intro hNotSelf hClaim
  cases hClaim with
  | inl hSelf =>
      exact False.elim (hNotSelf hSelf)
  | inr hBootstrap =>
      exact hBootstrap

def ChannelCompiler : CompilerCandidateFlow :=
  [[BMark.b0], [BMark.b1, BMark.b0], [BMark.b1, BMark.b1]]

def ChannelCompilerBehavior : CompilerBehaviorRelation :=
  fun C S T =>
    C = ChannelCompiler /\ T = [FlowEncoding S]

def ChannelFullCompiler (C : CompilerCandidateFlow) : Prop :=
  SelfHostingCompilerFlow ChannelCompilerBehavior C

theorem channel_compiler_not_full :
    Not (ChannelFullCompiler ChannelCompiler) := by
  intro hFull
  cases hFull.right.right with
  | intro C' hC' =>
      cases hC' with
      | intro _L hLedger =>
          have hForward :
              forall S T : EventFlow,
                ChannelCompilerBehavior ChannelCompiler S T ->
                  ChannelCompilerBehavior C' S T :=
            hLedger.right.left.right.right.left
          have hCompiled : ChannelCompilerBehavior ChannelCompiler
              ChannelCompiler C' :=
            hLedger.left
          have hCeq : C' = ChannelCompiler :=
            (hForward ChannelCompiler C' hCompiled).left
          have hCode : C' = [FlowEncoding ChannelCompiler] :=
            hCompiled.right
          have hImpossible :
              [FlowEncoding ChannelCompiler] = ChannelCompiler :=
            Eq.trans (Eq.symm hCode) hCeq
          simp [ChannelCompiler, FlowEncoding, EventEncoding, BodyEncoding,
            EventTerminator] at hImpossible

structure CompilerBootstrapLadder where
  C0 : CompilerCandidateFlow
  C1 : CompilerCandidateFlow
  C2 : CompilerCandidateFlow
  C3 : CompilerCandidateFlow
  C4 : CompilerCandidateFlow
  C5 : CompilerCandidateFlow

def LadderTransitionCertificate
    (source target certificate : EventFlow) : Prop :=
  exists RK : EventFlow,
    CompilerCertificateRecognition RK certificate target /\
      P9Subflow certificate source

def LadderSoundness (L : CompilerBootstrapLadder) : Prop :=
  exists K01 K12 K23 K34 K45 : EventFlow,
    LadderTransitionCertificate L.C0 L.C1 K01 /\
      LadderTransitionCertificate L.C1 L.C2 K12 /\
      LadderTransitionCertificate L.C2 L.C3 K23 /\
      LadderTransitionCertificate L.C3 L.C4 K34 /\
      LadderTransitionCertificate L.C4 L.C5 K45

def StagedHiddenInputsDischarged
    (behavior : CompilerBehaviorRelation) (L : CompilerBootstrapLadder) :
    Prop :=
  LadderSoundness L /\ SelfHostingCompilerFlow behavior L.C5

theorem sound_ladder_discharges
    {behavior : CompilerBehaviorRelation} {L : CompilerBootstrapLadder} :
    LadderSoundness L ->
      SelfHostingCompilerFlow behavior L.C5 ->
        StagedHiddenInputsDischarged behavior L := by
  intro hSound hSelf
  exact ⟨hSound, hSelf⟩

def BootstrapUndischarged (C : CompilerCandidateFlow) : Prop :=
  Not (CertifiedCompiler C) \/
    (forall behavior : CompilerBehaviorRelation,
      Not (SelfHostingCompilerFlow behavior C))

def RemainingBootstrapBoundary (C : CompilerCandidateFlow) : Prop :=
  BootstrapUndischarged C /\ BootstrapRecorded C

theorem remaining_bootstrap_boundary_visible {C : CompilerCandidateFlow} :
    RemainingBootstrapBoundary C -> BootstrapRecorded C := by
  intro hBoundary
  exact hBoundary.right

theorem invisible_bootstrap_blocks_certification {C : CompilerCandidateFlow} :
    BootstrapUndischarged C ->
      Not (BootstrapRecorded C) ->
        Not (RemainingBootstrapBoundary C) := by
  intro _hUndischarged hNotRecorded hBoundary
  exact hNotRecorded hBoundary.right

inductive CompilerTheoremTopic : Type where
  | channelRoundTrip
  | decodeEncode
  | recognizerSoundness
  | recognizerCompleteness
  | compilerSelfHosting
  | bootstrapDischarge

def CompilerTheoremPackage (T : TheoremCandidateFlow) : Prop :=
  TheoremFlow T /\ exists _topic : CompilerTheoremTopic, NonemptyEventFlow T

theorem compiler_theorem_code_is_theorem_code
    {T : TheoremCandidateFlow} :
    CompilerTheoremPackage T -> TheoremCode T = FlowEncoding T := by
  intro hPackage
  exact theorem_code_not_separate hPackage.left

theorem self_hosting_channel_bijection_independent :
    (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c ->
          exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c) := by
  exact channel_encoding_bijection

theorem channel_correctness_separate :
    ((forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c ->
          exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c)) /\
      Not (ChannelFullCompiler ChannelCompiler) := by
  constructor
  · exact self_hosting_channel_bijection_independent
  · exact channel_compiler_not_full

theorem compiler_flow_recognition_conservativity
    {C : CompilerCandidateFlow} {w : RawEvent} {m : DisplayAlphabet} :
    List.Mem w C -> List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro hEvent hMark
  exact event_flow_conservativity hEvent hMark

def P9CompilerCandidate (S C : EventFlow) : Prop :=
  P9Subflow S C

def P9RecognizesCompiler (RC S C : EventFlow) : Prop :=
  P9CompilerCandidate S C /\
    FormalCompilerInput (CompilerDatum.recognizedFlow RC C)

def P9RecognizedCompilerFlow (S C : EventFlow) : Prop :=
  exists RC : EventFlow, P9RecognizesCompiler RC S C

def P9CompilerCertificateCandidate (S KC C : EventFlow) : Prop :=
  P9Subflow S KC /\ P9CompilerCandidate S C

def P9RecognizesCompilerCert (RK S KC C : EventFlow) : Prop :=
  P9CompilerCertificateCandidate S KC C /\
    FormalCompilerInput (CompilerDatum.recognizedFlow RK KC) /\
    P9RecognizedCompilerFlow S C

def P9CertifiedCompiler (C : EventFlow) : Prop :=
  exists S : EventFlow, exists KC : EventFlow, exists RK : EventFlow,
    P9RecognizesCompilerCert RK S KC C

def P9FormalCompilationJudgment
    (Compiles : CompilerBehaviorRelation)
    (C S T : EventFlow) : Prop :=
  P9CertifiedCompiler C /\ Compiles C S T

theorem p9_uncertified_cannot_compile
    {Compiles : CompilerBehaviorRelation}
    {C S T : EventFlow} :
    Not (P9CertifiedCompiler C) ->
      Not (P9FormalCompilationJudgment Compiles C S T) := by
  intro hUncertified hJudgment
  exact hUncertified hJudgment.left

end BEDC.GroundCompiler.SelfHostingCompilerFlow
