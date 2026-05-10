import BEDC.GroundCompiler.SelfHostingCompilerFlow

namespace BEDC.GroundCompiler.SelfHostingReports

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.SelfHostingCompilerFlow

inductive P9CannotClaimKind : Type where
  | recognizedCompilerNotCertified
  | certifiedCompilerNotSelfHosting
  | selfCompilationNotBehaviorEquivalence
  | behaviorEquivalenceNotRawEquality
  | obligationsBlockFullDischarge
  | hostExecutableNotCompilerIdentity
  | binaryHashNotCompilerFlow
  | globalVerificationNotNewTheorem
  | implementationReportNotProof
  | fullClaimRequiresNoRemainingObligations

def P9CannotClaimAnnotations : Type :=
  List P9CannotClaimKind

def CompleteP9CannotClaimAnnotations
    (claims : P9CannotClaimAnnotations) : Prop :=
  List.Mem P9CannotClaimKind.recognizedCompilerNotCertified claims /\
    List.Mem P9CannotClaimKind.certifiedCompilerNotSelfHosting claims /\
    List.Mem P9CannotClaimKind.selfCompilationNotBehaviorEquivalence claims /\
    List.Mem P9CannotClaimKind.behaviorEquivalenceNotRawEquality claims /\
    List.Mem P9CannotClaimKind.obligationsBlockFullDischarge claims /\
    List.Mem P9CannotClaimKind.hostExecutableNotCompilerIdentity claims /\
    List.Mem P9CannotClaimKind.binaryHashNotCompilerFlow claims /\
    List.Mem P9CannotClaimKind.globalVerificationNotNewTheorem claims /\
    List.Mem P9CannotClaimKind.implementationReportNotProof claims /\
    List.Mem P9CannotClaimKind.fullClaimRequiresNoRemainingObligations claims

structure P9Report where
  decodedFlow : EventFlow
  compilerCandidates : List EventFlow
  recognizedCompilerFlows : List EventFlow
  certifiedCompilerFlows : List EventFlow
  behaviorRecords : List EventFlow
  selfCompilationFlows : List EventFlow
  behaviorEquivalenceFlows : List EventFlow
  selfHostingLedgers : List EventFlow
  bootstrapObligations : List EventFlow
  fullyDischargedClaims : List EventFlow
  globalVerificationFlows : List EventFlow
  noHostLeakAudits : List EventFlow
  implementationTargetAudits : List EventFlow
  remainingObligations : List EventFlow
  warnings : List EventFlow
  cannotClaims : P9CannotClaimAnnotations

def P9SelfHostingSupport (report : P9Report) : Prop :=
  exists certified selfCompilation behaviorEquivalence ledger : EventFlow,
    List.Mem certified report.certifiedCompilerFlows /\
      List.Mem selfCompilation report.selfCompilationFlows /\
      List.Mem behaviorEquivalence report.behaviorEquivalenceFlows /\
      List.Mem ledger report.selfHostingLedgers

def P9FullNoHiddenSupport (report : P9Report) : Prop :=
  report.remainingObligations = []

structure P9CompilerFieldStatus where
  compilerCandidate : EventFlow
  recognizedCompilerFlow : EventFlow
  compilerCertificateFlow : EventFlow
  inputDomainFlow : EventFlow
  outputDomainFlow : EventFlow
  encodingRuleFlow : EventFlow
  decodingRuleFlow : EventFlow
  roundTripProofFlow : EventFlow
  recognizerHierarchyFlow : EventFlow
  ledgerFlow : EventFlow
  failureFlow : EventFlow
  noHostLeakFlow : EventFlow
  kernelConservativityFlow : EventFlow
  selfDescriptionFlow : EventFlow
  sealFlow : EventFlow

inductive P9SelfHostingStatusKind : Type where
  | notSelfHosting
  | selfHostingWithObligations
  | fullyDischarged

inductive P9CompilerStatusTag : Type where
  | compilerCandidate
  | recognizedCompilerFlow
  | certifiedCompilerFlow
  | selfCompilingCompilerFlow
  | selfHostingCompilerFlow
  | selfHostingWithObligations
  | fullyDischargedCompilerFlow

structure P9SelfHostingStatusRecord where
  compilerFlow : EventFlow
  selfCompilationFlow : EventFlow
  outputCompilerFlow : EventFlow
  behaviorEquivalenceFlow : EventFlow
  selfCompilationLedger : EventFlow
  dischargedObligations : List EventFlow
  remainingObligations : List EventFlow
  noHostLeakAudit : EventFlow
  status : P9SelfHostingStatusKind

structure P9AuditChecklist where
  includesP8Requirements : Prop
  separatesCompilerCandidates : Prop
  recognizedRequiresGeneratedRecognizer : Prop
  separatesRecognizedFromCertified : Prop
  certifiedRequiresCompleteCertificate : Prop
  separatesBehaviorRecordsFromHostExecution : Prop
  behaviorRecordsRequireSoundness : Prop
  separatesSelfCompilationCandidates : Prop
  selfCompilationRequiresLedger : Prop
  separatesBehaviorEquivalenceFromRawEquality : Prop
  recordsBootstrapObligations : Prop
  separatesObligationsFromFullDischarge : Prop
  requiresNoHostLeakAudit : Prop
  globalStatusRequiresVerificationFlow : Prop
  rejectsHostCompilerIdentity : Prop
  includesCannotClaimAnnotations : Prop

def P9AuditChecklistComplete (checklist : P9AuditChecklist) : Prop :=
  checklist.includesP8Requirements /\
    checklist.separatesCompilerCandidates /\
    checklist.recognizedRequiresGeneratedRecognizer /\
    checklist.separatesRecognizedFromCertified /\
    checklist.certifiedRequiresCompleteCertificate /\
    checklist.separatesBehaviorRecordsFromHostExecution /\
    checklist.behaviorRecordsRequireSoundness /\
    checklist.separatesSelfCompilationCandidates /\
    checklist.selfCompilationRequiresLedger /\
    checklist.separatesBehaviorEquivalenceFromRawEquality /\
    checklist.recordsBootstrapObligations /\
    checklist.separatesObligationsFromFullDischarge /\
    checklist.requiresNoHostLeakAudit /\
    checklist.globalStatusRequiresVerificationFlow /\
    checklist.rejectsHostCompilerIdentity /\
    checklist.includesCannotClaimAnnotations

structure SoundP9Report (report : P9Report) where
  recognizedCompilerBacked :
    forall C : EventFlow,
      List.Mem C report.recognizedCompilerFlows ->
        exists S : EventFlow, P9RecognizedCompilerFlow S C
  certifiedCompilerComplete :
    forall C : EventFlow,
      List.Mem C report.certifiedCompilerFlows ->
        P9CompleteCertifiedCompiler C
  behaviorRecordsSound :
    forall BC : EventFlow,
      List.Mem BC report.behaviorRecords ->
        exists Compiles : CompilerBehaviorRelation,
          exists C X Y : EventFlow,
            P9BehaviorSoundness Compiles BC C X Y
  selfCompilationLedgers :
    forall SC : EventFlow,
      List.Mem SC report.selfCompilationFlows ->
        exists C C' LSC : EventFlow, SelfCompilationLedger LSC C C'
  behaviorEquivalenceRecorded :
    forall BE : EventFlow,
      List.Mem BE report.behaviorEquivalenceFlows ->
        exists behavior : CompilerBehaviorRelation,
          exists C C' : EventFlow, P9BehaviorEquivalent behavior C' C
  selfHostingClaimsSupported : P9SelfHostingSupport report
  fullyDischargedOnlyWhenEmpty :
    (exists C : EventFlow, List.Mem C report.fullyDischargedClaims) ->
      report.remainingObligations = []
  globalVerificationSound :
    forall G : EventFlow,
      List.Mem G report.globalVerificationFlows ->
        GlobalVerificationSoundness G
  cannotClaimsComplete :
    CompleteP9CannotClaimAnnotations report.cannotClaims

theorem sound_p9_report_supports_self_hosting
    {report : P9Report} :
    SoundP9Report report -> P9SelfHostingSupport report := by
  intro hSound
  exact hSound.selfHostingClaimsSupported

theorem sound_p9_report_full_claim_requires_empty_obligations
    {report : P9Report} :
    SoundP9Report report ->
      (exists C : EventFlow, List.Mem C report.fullyDischargedClaims) ->
        P9FullNoHiddenSupport report := by
  intro hSound hFull
  exact hSound.fullyDischargedOnlyWhenEmpty hFull

theorem p9_statuses_distinct :
    Not (P9CompilerStatusTag.compilerCandidate =
      P9CompilerStatusTag.recognizedCompilerFlow) /\
    Not (P9CompilerStatusTag.recognizedCompilerFlow =
      P9CompilerStatusTag.certifiedCompilerFlow) /\
    Not (P9CompilerStatusTag.certifiedCompilerFlow =
      P9CompilerStatusTag.selfCompilingCompilerFlow) /\
    Not (P9CompilerStatusTag.selfCompilingCompilerFlow =
      P9CompilerStatusTag.selfHostingCompilerFlow) /\
    Not (P9CompilerStatusTag.selfHostingCompilerFlow =
      P9CompilerStatusTag.selfHostingWithObligations) /\
    Not (P9CompilerStatusTag.selfHostingWithObligations =
      P9CompilerStatusTag.fullyDischargedCompilerFlow) := by
  exact
    ⟨(fun h => nomatch h),
      (fun h => nomatch h),
      (fun h => nomatch h),
      (fun h => nomatch h),
      (fun h => nomatch h),
      (fun h => nomatch h)⟩

def P9AdequacySupport
    (checklist : P9AuditChecklist) (report : P9Report) : Prop :=
  P9AuditChecklistComplete checklist /\
    SoundP9Report report /\
    P9SelfHostingSupport report

theorem p9_adequacy
    {checklist : P9AuditChecklist} {report : P9Report} :
    P9AuditChecklistComplete checklist ->
      SoundP9Report report ->
        P9AdequacySupport checklist report := by
  intro hChecklist hReport
  exact ⟨hChecklist, hReport, sound_p9_report_supports_self_hosting hReport⟩

end BEDC.GroundCompiler.SelfHostingReports
