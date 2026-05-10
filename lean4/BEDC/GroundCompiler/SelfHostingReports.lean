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

end BEDC.GroundCompiler.SelfHostingReports
