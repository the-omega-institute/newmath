import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.TheoremGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def TheoremCandidateFlow : Type :=
  EventFlow

def GeneratedTheoremRecognizer : Type :=
  GeneratedRecognizer

def TheoremRecognitionRelation
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  RecognizesTheorem R T

def TheoremFlow (T : TheoremCandidateFlow) : Prop :=
  exists R : GeneratedTheoremRecognizer, TheoremRecognitionRelation R T

def TheoremCode (T : TheoremCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding T

inductive TheoremRole : Type where
  | statement
  | dependencies
  | proof
  | certificates
  | ledger
  | status
  | canonicalSite
  | closingSeal

def TheoremRoleSubflow
    (R : GeneratedTheoremRecognizer) (T part : TheoremCandidateFlow)
    (_role : TheoremRole) : Prop :=
  TheoremRecognitionRelation R T /\ NonemptyEventFlow part

def CompleteTheoremFlowRecognition
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists statement dependencies proof certificates ledger status canonicalSite
      sealFlow : EventFlow,
    TheoremRoleSubflow R T statement TheoremRole.statement /\
      TheoremRoleSubflow R T dependencies TheoremRole.dependencies /\
      TheoremRoleSubflow R T proof TheoremRole.proof /\
      TheoremRoleSubflow R T certificates TheoremRole.certificates /\
      TheoremRoleSubflow R T ledger TheoremRole.ledger /\
      TheoremRoleSubflow R T status TheoremRole.status /\
      TheoremRoleSubflow R T canonicalSite TheoremRole.canonicalSite /\
      TheoremRoleSubflow R T sealFlow TheoremRole.closingSeal

def GeneratedProofCheckerFlow : Type :=
  EventFlow

def ChecksProof
    (R : GeneratedProofCheckerFlow)
    (statement dependencies proof : TheoremCandidateFlow) : Prop :=
  NonemptyEventFlow R /\
    NonemptyEventFlow statement /\
    NonemptyEventFlow dependencies /\
    NonemptyEventFlow proof

def ProofSoundTheoremRecognition
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists statement dependencies proof : TheoremCandidateFlow,
    exists proofChecker : GeneratedProofCheckerFlow,
      TheoremRoleSubflow R T statement TheoremRole.statement /\
        TheoremRoleSubflow R T dependencies TheoremRole.dependencies /\
        TheoremRoleSubflow R T proof TheoremRole.proof /\
        ChecksProof proofChecker statement dependencies proof

theorem no_external_theorem_input :
    Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) :=
  structural_hidden_not_formal StructuralHiddenInput.hostTheoremIdentifier

theorem theorem_recognition_preserves_code
    {R : GeneratedTheoremRecognizer} {T : TheoremCandidateFlow} :
    TheoremRecognitionRelation R T -> TheoremCode T = FlowEncoding T := by
  intro _
  rfl

theorem theorem_code_not_separate {T : TheoremCandidateFlow} :
    TheoremFlow T -> TheoremCode T = FlowEncoding T := by
  intro _
  rfl

end BEDC.GroundCompiler.TheoremGenerated
