import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.DerivCertGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def GeneratedDerivCertRecognizer : Type :=
  GeneratedRecognizer

def DerivCertSourceSubflow (part whole : EventFlow) : Prop :=
  exists before after : EventFlow, whole = List.append before (List.append part after)

inductive DerivCertFieldRole : Type where
  | source
  | classifier
  | exactness
  | ledger
  | stability
  | strength

def DerivCertFieldSubflow
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (_role : DerivCertFieldRole) (part : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    DerivCertSourceSubflow part D

def DerivCertSealSubflow
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (sealFlow : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    DerivCertSourceSubflow sealFlow D

def CompleteSixFieldDerivCertRecognition
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow) : Prop :=
  exists source classifier exactness ledger stability strength sealFlow : EventFlow,
    DerivCertFieldSubflow R D DerivCertFieldRole.source source /\
      DerivCertFieldSubflow R D DerivCertFieldRole.classifier classifier /\
      DerivCertFieldSubflow R D DerivCertFieldRole.exactness exactness /\
      DerivCertFieldSubflow R D DerivCertFieldRole.ledger ledger /\
      DerivCertFieldSubflow R D DerivCertFieldRole.stability stability /\
      DerivCertFieldSubflow R D DerivCertFieldRole.strength strength /\
      DerivCertSealSubflow R D sealFlow

def RecognizesDerivCert
    (R : GeneratedDerivCertRecognizer) (D N s : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    StrengthEventFlow s /\
    CompleteSixFieldDerivCertRecognition R D

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

theorem no_derivcert_without_six_fields
    {R : GeneratedDerivCertRecognizer} {D N s : EventFlow} :
    RecognizesDerivCert R D N s ->
      CompleteSixFieldDerivCertRecognition R D := by
  intro h
  exact h.right.right.right

end BEDC.GroundCompiler.DerivCertGenerated
