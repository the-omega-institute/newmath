import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.DerivCertGenerated

open BEDC.GroundCompiler.EventFlow

def GeneratedDerivCertRecognizer : Type :=
  GeneratedRecognizer

def RecognizesDerivCert
    (R : GeneratedDerivCertRecognizer) (D N s : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    StrengthEventFlow s

def DerivCertFlow (D N s : EventFlow) : Prop :=
  exists R : GeneratedDerivCertRecognizer, RecognizesDerivCert R D N s

end BEDC.GroundCompiler.DerivCertGenerated
