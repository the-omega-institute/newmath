import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.RecognizerFlows

open BEDC.FKernel.Mark
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

def RecognizerCertificateField
    (Q : GeneratedRecognizer) (_C_R : RecognizerCertCandidateFlow)
    (X : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow Q X)

def RecognizerCertificateFields
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (D T rho snd cmp ledger failure stability recSeal : EventFlow) : Prop :=
  RecognizerCertificateField Q C_R D /\
    RecognizerCertificateField Q C_R T /\
    RecognizerCertificateField Q C_R rho /\
    RecognizerCertificateField Q C_R snd /\
    RecognizerCertificateField Q C_R cmp /\
    RecognizerCertificateField Q C_R ledger /\
    RecognizerCertificateField Q C_R failure /\
    RecognizerCertificateField Q C_R stability /\
    RecognizerCertificateField Q C_R recSeal

def RoleOK (rho : RecognitionRole) (S : EventFlow) : Prop :=
  NonemptyEventFlow rho /\
    FormalCompilerInput (CompilerDatum.recognizedFlow rho S)

def RecSound (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  forall S : EventFlow, Recognizes R rho S -> RoleOK rho S

def RecComplete
    (R : RecognizerCandidateFlow) (D : EventFlow) (rho : RecognitionRole) :
    Prop :=
  NonemptyEventFlow D /\
    forall S : EventFlow,
      FormalCompilerInput (CompilerDatum.recognizedFlow D S) ->
        RoleOK rho S -> Recognizes R rho S

def RecFailureLedger
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (F : EventFlow) : Prop :=
  RecognizerCertificateField Q C_R F /\ NonemptyEventFlow F

def RecLedger
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (L : EventFlow) : Prop :=
  RecognizerCertificateField Q C_R L /\ NonemptyEventFlow L

def RecognizerConservative
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  forall S : EventFlow,
    Recognizes R rho S ->
      forall w : RawEvent,
        List.Mem w S ->
          forall m : DisplayAlphabet,
            List.Mem m w -> m = BMark.b0 \/ m = BMark.b1

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

theorem certified_recognition_only
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} :
    CertifiedRecognizer R rho ->
      RecognizerConservative R rho ->
        forall S : EventFlow,
          Recognizes R rho S ->
            forall w : RawEvent,
              List.Mem w S ->
                forall m : DisplayAlphabet,
                  List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro _ hCons
  exact hCons

end BEDC.GroundCompiler.RecognizerFlows
