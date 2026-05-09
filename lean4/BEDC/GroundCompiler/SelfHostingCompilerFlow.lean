import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SelfHostingCompilerFlow

open BEDC.GroundCompiler.EventFlow

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
