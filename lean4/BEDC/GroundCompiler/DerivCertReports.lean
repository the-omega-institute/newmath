import BEDC.GroundCompiler.DerivCertGenerated
import BEDC.GroundCompiler.PackageNameCertPrototype

namespace BEDC.GroundCompiler.DerivCertReports

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.DerivCertGenerated
open BEDC.GroundCompiler.NameCertGenerated

inductive P6FieldStatus : Type where
  | present
  | missing
  | candidateOnly

structure DerivAcceptFieldStatus where
  source : P6FieldStatus
  classifier : P6FieldStatus
  exactness : P6FieldStatus
  ledger : P6FieldStatus
  stability : P6FieldStatus
  strength : P6FieldStatus
  derivSeal : P6FieldStatus
  nameCertFlow : P6FieldStatus
  derivCertFlow : P6FieldStatus
  strengthFlow : P6FieldStatus
  gateSeal : P6FieldStatus

inductive P6CannotClaimKind : Type where
  | nameCertAloneAcceptedExport
  | derivCertAloneAcceptedExport
  | strengthAloneDerivCert
  | codeObjectEquality
  | codeProof
  | codeBridgeCert
  | retroactivePromotion
  | classifierEquivalenceFlowEquality
  | reportProof

def P6CannotClaimAnnotations : Type :=
  List P6CannotClaimKind

def CompleteP6CannotClaimAnnotations
    (claims : P6CannotClaimAnnotations) : Prop :=
  List.Mem P6CannotClaimKind.nameCertAloneAcceptedExport claims /\
    List.Mem P6CannotClaimKind.derivCertAloneAcceptedExport claims /\
    List.Mem P6CannotClaimKind.strengthAloneDerivCert claims /\
    List.Mem P6CannotClaimKind.codeObjectEquality claims /\
    List.Mem P6CannotClaimKind.codeProof claims /\
    List.Mem P6CannotClaimKind.codeBridgeCert claims /\
    List.Mem P6CannotClaimKind.retroactivePromotion claims /\
    List.Mem P6CannotClaimKind.classifierEquivalenceFlowEquality claims /\
    List.Mem P6CannotClaimKind.reportProof claims

structure P6AcceptedCodeEvidence where
  acceptedGate : EventFlow
  name : EventFlow
  strength : EventFlow
  nameCertFlow : EventFlow
  derivCertFlow : EventFlow
  accepted : AcceptedFlow acceptedGate name strength
  nameCert : NameCertFlow nameCertFlow name
  derivCert : DerivCertFlow derivCertFlow name strength

structure P6Report where
  decodedEventFlow : EventFlow
  outputView : P6Output
  recognizedNameCertFlows : List (EventFlow × EventFlow)
  derivCertCandidates : List (EventFlow × EventFlow × EventFlow)
  recognizedDerivCertFlows : List (EventFlow × EventFlow × EventFlow)
  fieldStatus : List DerivAcceptFieldStatus
  recognizedStrengthFlows : List (EventFlow × EventFlow)
  acceptGateCandidates : List (EventFlow × EventFlow × EventFlow)
  recognizedAcceptGateFlows : List (EventFlow × EventFlow × EventFlow)
  acceptedCodeEvidence : List P6AcceptedCodeEvidence
  acceptedObjectCodes : List (List DisplayAlphabet)
  missingFields : List EventFlow
  upgradeStatus : List (EventFlow × EventFlow × EventFlow × EventFlow)
  warnings : List EventFlow
  cannotClaims : P6CannotClaimAnnotations

structure SoundP6Report where
  fieldStatus : List DerivAcceptFieldStatus
  acceptedCodeEvidence : List P6AcceptedCodeEvidence
  cannotClaims : P6CannotClaimAnnotations
  completeCannotClaims : CompleteP6CannotClaimAnnotations cannotClaims

theorem sound_p6_report
    {report : SoundP6Report} {entry : P6AcceptedCodeEvidence} :
    List.Mem entry report.acceptedCodeEvidence ->
      exists C D : EventFlow,
        NameCertFlow C entry.name /\
          DerivCertFlow D entry.name entry.strength := by
  intro _
  exact ⟨entry.nameCertFlow, entry.derivCertFlow, entry.nameCert,
    entry.derivCert⟩

theorem sound_accepted_code_certificate_mediated
    {report : SoundP6Report} {entry : P6AcceptedCodeEvidence} :
    List.Mem entry report.acceptedCodeEvidence ->
      exists C D : EventFlow,
        NameCertFlow C entry.name /\
          DerivCertFlow D entry.name entry.strength :=
  sound_p6_report

theorem p6_code_not_theoremhood {report : SoundP6Report} :
    List.Mem P6CannotClaimKind.codeProof report.cannotClaims := by
  exact report.completeCannotClaims.right.right.right.right.left

structure P6AuditChecklist
    (prototype : DerivAcceptPrototype) (report : P6Report)
    (p5Prototype : PackageNameCertPrototype.PkgNameCertPrototype)
    (p5Report : PackageNameCertPrototype.P5Report) where
  p5Audit : PackageNameCertPrototype.P5AuditChecklist p5Prototype p5Report
  derivCertCandidatesSeparated :
    forall {D N s : EventFlow},
      List.Mem (P6ReportDatum.derivCertCandidate D N s) report.outputView ->
        (forall R : GeneratedDerivCertRecognizer,
          Not
            (List.Mem (P6ReportDatum.recognizedDerivCert R D N s)
              report.outputView)) ->
          Not (DerivCertFlow D N s)
  recognizedDerivCertsGenerated :
    forall {R : GeneratedDerivCertRecognizer} {D N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedDerivCert R D N s)
          report.outputView ->
        RecognizesDerivCert R D N s
  derivCertsHaveSixFields :
    forall {R : GeneratedDerivCertRecognizer} {D N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedDerivCert R D N s)
          report.outputView ->
        CompleteSixFieldDerivCertRecognition R D
  derivCertFieldSoundness :
    forall {R : GeneratedDerivCertRecognizer} {D N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedDerivCert R D N s)
          report.outputView ->
        exists source classifier exactness ledger stability strength : EventFlow,
          DerivCertFieldSoundness R D N s source classifier exactness ledger
            stability strength
  strengthCandidatesSeparated :
    forall {ambient s : EventFlow},
      List.Mem (P6ReportDatum.strengthCandidate ambient s) report.outputView ->
        (forall R : GeneratedStrengthRecognizer,
          forall sigma : StrengthRole,
            Not
              (List.Mem
                (P6ReportDatum.recognizedStrength R ambient s sigma)
                report.outputView)) ->
          Not (StrengthEventFlow s)
  recognizedStrengthsGenerated :
    forall {R : GeneratedStrengthRecognizer} {ambient s : EventFlow}
      {sigma : StrengthRole},
      List.Mem (P6ReportDatum.recognizedStrength R ambient s sigma)
          report.outputView ->
        RecognizesStrength R s sigma
  acceptGateCandidatesSeparated :
    forall {A N s : EventFlow},
      List.Mem (P6ReportDatum.acceptGateCandidate A N s) report.outputView ->
        (forall R : GeneratedAcceptGateRecognizer,
          Not
            (List.Mem (P6ReportDatum.recognizedAcceptGate R A N s)
              report.outputView)) ->
          Not (AcceptedFlow A N s)
  recognizedAcceptGatesGenerated :
    forall {R : GeneratedAcceptGateRecognizer} {A N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedAcceptGate R A N s)
          report.outputView ->
        RecognizesAcceptGate R report.decodedEventFlow A N s
  matchingNameDerivRequired :
    forall {R : GeneratedAcceptGateRecognizer} {A N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedAcceptGate R A N s)
          report.outputView ->
        exists C D : EventFlow, NameCertFlow C N /\ DerivCertFlow D N s
  acceptedCodeFromGate :
    forall {A N s : EventFlow},
      List.Mem (P6ReportDatum.acceptedObjectCode A N s) report.outputView ->
        AcceptedFlow A N s
  missingFieldsReported :
    forall {candidate : EventFlow},
      List.Mem (P6ReportDatum.missingField candidate) report.outputView ->
        FormalCompilerInput (CompilerDatum.eventFlow candidate)
  acceptedCodeDistinguishedFromObjectEquality :
    List.Mem P6CannotClaimKind.codeObjectEquality report.cannotClaims
  noRetroactivePromotionRecorded :
    List.Mem P6CannotClaimKind.retroactivePromotion report.cannotClaims
  theoremhoodNotInferred :
    List.Mem P6CannotClaimKind.codeProof report.cannotClaims
  cannotClaimAnnotationsComplete :
    CompleteP6CannotClaimAnnotations report.cannotClaims

structure P6Adequate
    (prototype : DerivAcceptPrototype) (report : P6Report)
    (p5Prototype : PackageNameCertPrototype.PkgNameCertPrototype)
    (p5Report : PackageNameCertPrototype.P5Report) where
  audit : P6AuditChecklist prototype report p5Prototype p5Report
  p5Adequate : PackageNameCertPrototype.P5Adequate p5Prototype p5Report
  derivCertRecognitionBacked :
    forall {R : GeneratedDerivCertRecognizer} {D N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedDerivCert R D N s)
          report.outputView ->
        RecognizesDerivCert R D N s
  acceptGateRecognitionBacked :
    forall {R : GeneratedAcceptGateRecognizer} {A N s : EventFlow},
      List.Mem (P6ReportDatum.recognizedAcceptGate R A N s)
          report.outputView ->
        RecognizesAcceptGate R report.decodedEventFlow A N s
  acceptedObjectCodesMediated :
    forall {entry : P6AcceptedCodeEvidence},
      List.Mem entry report.acceptedCodeEvidence ->
        exists C D : EventFlow,
          NameCertFlow C entry.name /\
            DerivCertFlow D entry.name entry.strength
  cannotClaimsComplete : CompleteP6CannotClaimAnnotations report.cannotClaims

theorem p6_adequacy
    {prototype : DerivAcceptPrototype} {report : P6Report}
    {p5Prototype : PackageNameCertPrototype.PkgNameCertPrototype}
    {p5Report : PackageNameCertPrototype.P5Report} :
    P6AuditChecklist prototype report p5Prototype p5Report ->
      P6Adequate prototype report p5Prototype p5Report := by
  intro hAudit
  exact
    { audit := hAudit,
      p5Adequate := PackageNameCertPrototype.p5_adequacy hAudit.p5Audit,
      derivCertRecognitionBacked := hAudit.recognizedDerivCertsGenerated,
      acceptGateRecognitionBacked := hAudit.recognizedAcceptGatesGenerated,
      acceptedObjectCodesMediated := by
        intro entry _
        exact
          ⟨entry.nameCertFlow, entry.derivCertFlow, entry.nameCert,
            entry.derivCert⟩,
      cannotClaimsComplete := hAudit.cannotClaimAnnotationsComplete }

theorem p6_adequacy_does_not_imply_higher {report : SoundP6Report} :
    List.Mem P6CannotClaimKind.codeProof report.cannotClaims /\
      List.Mem P6CannotClaimKind.codeBridgeCert report.cannotClaims /\
      List.Mem P6CannotClaimKind.reportProof report.cannotClaims := by
  constructor
  · exact report.completeCannotClaims.right.right.right.right.left
  constructor
  · exact report.completeCannotClaims.right.right.right.right.right.left
  · exact report.completeCannotClaims.right.right.right.right.right.right.right.right

theorem p6_conservative_over_finite_kernel
    {A N s : EventFlow} {w : RawEvent} {m : DisplayAlphabet} :
    P6AcceptedObjectFlow A N s ->
      List.Mem w A -> List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro hAccepted hMemEvent hMemMark
  exact accepted_flow_recognition_conservativity hAccepted hMemEvent hMemMark

theorem p6_not_proof_engine {report : SoundP6Report} :
    List.Mem P6CannotClaimKind.codeProof report.cannotClaims /\
      List.Mem P6CannotClaimKind.reportProof report.cannotClaims := by
  constructor
  · exact report.completeCannotClaims.right.right.right.right.left
  · exact report.completeCannotClaims.right.right.right.right.right.right.right.right

end BEDC.GroundCompiler.DerivCertReports
