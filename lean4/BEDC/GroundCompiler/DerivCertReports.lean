import BEDC.GroundCompiler.DerivCertGenerated

namespace BEDC.GroundCompiler.DerivCertReports

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

end BEDC.GroundCompiler.DerivCertReports
