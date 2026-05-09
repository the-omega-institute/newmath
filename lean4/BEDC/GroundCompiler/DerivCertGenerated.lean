import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.DerivCertGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def GeneratedDerivCertRecognizer : Type :=
  GeneratedRecognizer

def RecognizesDerivCert
    (R : GeneratedDerivCertRecognizer) (D N s : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    StrengthEventFlow s

def DerivCertFlow (D N s : EventFlow) : Prop :=
  exists R : GeneratedDerivCertRecognizer, RecognizesDerivCert R D N s

def DerivCertCode (D _N _s : EventFlow) : List DisplayAlphabet :=
  FlowEncoding D

theorem no_external_derivcert_input :
    Not (FormalCompilerInput CompilerDatum.hostDerivCert) :=
  structural_hidden_not_formal StructuralHiddenInput.hostDerivCert

theorem derivcert_recognition_preserves_code
    {R : GeneratedDerivCertRecognizer} {D N s : EventFlow} :
    RecognizesDerivCert R D N s -> DerivCertCode D N s = FlowEncoding D := by
  intro _
  rfl

theorem derivcert_code_not_separate
    {D N s : EventFlow} :
    DerivCertFlow D N s -> DerivCertCode D N s = FlowEncoding D := by
  intro _
  rfl

end BEDC.GroundCompiler.DerivCertGenerated
