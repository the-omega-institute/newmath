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

end BEDC.GroundCompiler.RecognizerFlows
