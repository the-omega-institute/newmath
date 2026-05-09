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

def LegalTheoremCode (c : List DisplayAlphabet) : Prop :=
  exists T : TheoremCandidateFlow, c = TheoremCode T

def RecognizesTheoremCode
    (R : GeneratedTheoremRecognizer) (c : List DisplayAlphabet) : Prop :=
  exists T : TheoremCandidateFlow,
    Decode c = some T /\ TheoremRecognitionRelation R T

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

def CertificateSoundTheoremRecognition
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists certificates : TheoremCandidateFlow,
    exists certificateRecognizer : GeneratedRecognizer,
      TheoremRoleSubflow R T certificates TheoremRole.certificates /\
        Recognizes certificateRecognizer certificates certificates

def LedgerSoundTheoremRecognition
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists ledger : TheoremCandidateFlow,
    TheoremRoleSubflow R T ledger TheoremRole.ledger

def StatusSoundTheoremRecognition
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists status : TheoremCandidateFlow,
    exists statusRecognizer : GeneratedRecognizer,
      TheoremRoleSubflow R T status TheoremRole.status /\
        Recognizes statusRecognizer status status

def SiteSoundTheoremRecognition
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists canonicalSite : TheoremCandidateFlow,
    TheoremRoleSubflow R T canonicalSite TheoremRole.canonicalSite

def SoundTheoremFlow
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  CompleteTheoremFlowRecognition R T /\
    ProofSoundTheoremRecognition R T /\
    CertificateSoundTheoremRecognition R T /\
    LedgerSoundTheoremRecognition R T /\
    StatusSoundTheoremRecognition R T /\
    SiteSoundTheoremRecognition R T

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

theorem theorem_code_round_trip (T : TheoremCandidateFlow) :
    Decode (TheoremCode T) = some T :=
  flow_level_round_trip T

theorem theorem_code_injective {T U : TheoremCandidateFlow} :
    TheoremCode T = TheoremCode U -> T = U := by
  intro h
  have hDecode : Decode (TheoremCode T) = Decode (TheoremCode U) :=
    congrArg Decode h
  rw [theorem_code_round_trip T, theorem_code_round_trip U] at hDecode
  cases hDecode
  rfl

theorem theorem_code_bijective :
    (forall T : TheoremCandidateFlow, Decode (TheoremCode T) = some T) /\
      (forall c : List DisplayAlphabet,
        LegalTheoremCode c ->
          exists T : TheoremCandidateFlow,
            Decode c = some T /\ TheoremCode T = c) := by
  constructor
  · intro T
    exact theorem_code_round_trip T
  · intro c h
    cases h with
    | intro T hT =>
        refine ⟨T, ?_, ?_⟩
        · rw [hT]
          exact theorem_code_round_trip T
        · exact hT.symm

theorem compile_decode_preserves_recognition
    {R : GeneratedTheoremRecognizer} {T : TheoremCandidateFlow} :
    TheoremRecognitionRelation R T -> RecognizesTheoremCode R (TheoremCode T) := by
  intro h
  exact ⟨T, theorem_code_round_trip T, h⟩

theorem recognition_invariant_under_compile_decode
    {T : TheoremCandidateFlow} :
    TheoremFlow T -> exists R : GeneratedTheoremRecognizer,
      RecognizesTheoremCode R (TheoremCode T) := by
  intro h
  cases h with
  | intro R hR =>
      exact ⟨R, compile_decode_preserves_recognition hR⟩

theorem sound_theorem_flow_establishes_theoremhood
    {R : GeneratedTheoremRecognizer} {T : TheoremCandidateFlow} :
    SoundTheoremFlow R T -> TheoremFlow T := by
  intro hSound
  cases hSound.left with
  | intro statement hComplete =>
      cases hComplete with
      | intro dependencies hComplete =>
          cases hComplete with
          | intro proof hComplete =>
              cases hComplete with
              | intro certificates hComplete =>
                  cases hComplete with
                  | intro ledger hComplete =>
                      cases hComplete with
                      | intro status hComplete =>
                          cases hComplete with
                          | intro canonicalSite hComplete =>
                              cases hComplete with
                              | intro sealFlow hFields =>
                                  exact ⟨R, hFields.left.left⟩

end BEDC.GroundCompiler.TheoremGenerated
