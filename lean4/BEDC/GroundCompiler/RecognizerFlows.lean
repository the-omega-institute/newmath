import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.RecognizerFlows

open BEDC.GroundCompiler.EventFlow

def RecognizerCertCandidateFlow : Type :=
  EventFlow

def RecognizesRecognizerCert
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  NonemptyEventFlow C_R /\
    FormalCompilerInput (CompilerDatum.recognizedFlow Q C_R) /\
    FormalCompilerInput (CompilerDatum.recognizedFlow R rho)

def CertifiedRecognizer
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  exists C_R : RecognizerCertCandidateFlow,
    exists Q : GeneratedRecognizer,
      RecognizesRecognizerCert Q C_R R rho

def RoleOK (rho : RecognitionRole) (S : EventFlow) : Prop :=
  NonemptyEventFlow rho /\
    FormalCompilerInput (CompilerDatum.recognizedFlow rho S)

def RecSound (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  forall S : EventFlow, Recognizes R rho S -> RoleOK rho S

def FormalRecognitionEvidence
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) (S : EventFlow) :
    Prop :=
  CertifiedRecognizer R rho /\ Recognizes R rho S

theorem formal_recognition_evidence_requires_certified
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    FormalRecognitionEvidence R rho S -> CertifiedRecognizer R rho := by
  intro h
  exact h.left

theorem uncertified_cannot_license
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    Not (CertifiedRecognizer R rho) ->
      Not (FormalRecognitionEvidence R rho S) := by
  intro hNotCert hEvidence
  exact hNotCert (formal_recognition_evidence_requires_certified hEvidence)

end BEDC.GroundCompiler.RecognizerFlows
