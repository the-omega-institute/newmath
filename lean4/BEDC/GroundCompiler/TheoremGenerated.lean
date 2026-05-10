import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SourceChannel

namespace BEDC.GroundCompiler.TheoremGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.SourceChannel

def TheoremCandidateFlow : Type :=
  EventFlow

def GeneratedTheoremRecognizer : Type :=
  GeneratedRecognizer

def TheoremRecognitionRelation
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  RecognizesTheorem R T

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

def TheoremSourceSubflow (part whole : EventFlow) : Prop :=
  exists before after : EventFlow, whole = List.append before (List.append part after)

def TheoremSealSubflow
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow)
    (sealFlow : EventFlow) : Prop :=
  TheoremRoleSubflow R T sealFlow TheoremRole.closingSeal /\
    TheoremSourceSubflow sealFlow T

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

def TheoremFlow (T : TheoremCandidateFlow) : Prop :=
  exists R : GeneratedTheoremRecognizer,
    TheoremRecognitionRelation R T /\ CompleteTheoremFlowRecognition R T

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

def AcceptedTheoremFlow (T : TheoremCandidateFlow) : Prop :=
  exists R : GeneratedTheoremRecognizer, SoundTheoremFlow R T

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

theorem no_theorem_recognition_by_channel_substring :
    (exists c u : List DisplayAlphabet,
      LegalZStream c /\
        ContiguousSubstring u c /\
        Not (OccursAsDecodedEvent u c)) /\
      (forall R : GeneratedTheoremRecognizer,
        forall c : List DisplayAlphabet,
          RecognizesTheoremCode R c ->
            exists T : TheoremCandidateFlow,
              Decode c = some T /\ TheoremRecognitionRelation R T) := by
  constructor
  · exact channel_substring_not_source_event
  · intro _ _ hCode
    exact hCode

theorem recognition_invariant_under_compile_decode
    {T : TheoremCandidateFlow} :
    TheoremFlow T -> exists R : GeneratedTheoremRecognizer,
      RecognizesTheoremCode R (TheoremCode T) := by
  intro h
  cases h with
  | intro R hR =>
      exact ⟨R, compile_decode_preserves_recognition hR.left⟩

theorem empty_not_theorem_recognition_relation
    (R : GeneratedTheoremRecognizer) :
    Not (TheoremRecognitionRelation R []) := by
  intro h
  exact empty_not_nonempty_event_flow h.right

theorem empty_not_proof_sound
    (R : GeneratedTheoremRecognizer) :
    Not (ProofSoundTheoremRecognition R []) := by
  intro h
  cases h with
  | intro statement hStatement =>
      cases hStatement with
      | intro dependencies hDependencies =>
          cases hDependencies with
          | intro proof hProof =>
              cases hProof with
              | intro proofChecker hFields =>
                  exact empty_not_theorem_recognition_relation R hFields.left.left

theorem empty_not_accepted_theorem_flow :
    Not (AcceptedTheoremFlow []) := by
  intro h
  cases h with
  | intro R hSound =>
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
                                      exact
                                        empty_not_theorem_recognition_relation R
                                          hFields.left.left

theorem theorem_code_existence_not_accepted :
    exists c : List DisplayAlphabet,
      LegalTheoremCode c /\
        exists T : TheoremCandidateFlow,
          Decode c = some T /\ Not (AcceptedTheoremFlow T) := by
  refine ⟨TheoremCode [], ?_, ?_⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], theorem_code_round_trip [], empty_not_accepted_theorem_flow⟩

theorem theorem_code_is_not_proof :
    exists c : List DisplayAlphabet,
      LegalTheoremCode c /\
        exists T : TheoremCandidateFlow,
          Decode c = some T /\
            (forall R : GeneratedTheoremRecognizer,
              Not (ProofSoundTheoremRecognition R T)) := by
  refine ⟨TheoremCode [], ?_, ?_⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], theorem_code_round_trip [], empty_not_proof_sound⟩

theorem theorem_seal_is_source_subflow
    {R : GeneratedTheoremRecognizer} {T : TheoremCandidateFlow}
    {sealFlow : EventFlow} :
    TheoremSealSubflow R T sealFlow -> TheoremSourceSubflow sealFlow T := by
  intro hSeal
  exact hSeal.right

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
                                  exact ⟨R, hFields.left.left, hSound.left⟩

theorem no_theorem_without_complete_recognition
    {T : TheoremCandidateFlow} :
    TheoremFlow T ->
      exists R : GeneratedTheoremRecognizer,
        TheoremRecognitionRelation R T /\ CompleteTheoremFlowRecognition R T := by
  intro h
  exact h

theorem incomplete_theorem_flow_not_theorem
    {T : TheoremCandidateFlow} :
    (forall R : GeneratedTheoremRecognizer,
      TheoremRecognitionRelation R T ->
        Not (CompleteTheoremFlowRecognition R T)) ->
      Not (TheoremFlow T) := by
  intro hIncomplete hFlow
  cases hFlow with
  | intro R hRecognizes =>
      exact hIncomplete R hRecognizes.left hRecognizes.right

theorem statement_alone_not_theorem
    {T : TheoremCandidateFlow} :
    (exists R : GeneratedTheoremRecognizer,
      exists statement : TheoremCandidateFlow,
        TheoremRoleSubflow R T statement TheoremRole.statement) ->
      (forall R : GeneratedTheoremRecognizer,
        TheoremRecognitionRelation R T ->
          forall proof : TheoremCandidateFlow,
            Not (TheoremRoleSubflow R T proof TheoremRole.proof)) ->
        Not (TheoremFlow T) := by
  intro _ hNoProof hFlow
  cases hFlow with
  | intro R hRecognizes =>
      cases hRecognizes.right with
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
                                      exact hNoProof R hRecognizes.left proof
                                        hFields.right.right.left

theorem proof_alone_not_theorem
    {T : TheoremCandidateFlow} :
    (exists R : GeneratedTheoremRecognizer,
      exists proof : TheoremCandidateFlow,
        TheoremRoleSubflow R T proof TheoremRole.proof) ->
      (forall R : GeneratedTheoremRecognizer,
        TheoremRecognitionRelation R T ->
          Not (CompleteTheoremFlowRecognition R T)) ->
        Not (TheoremFlow T) := by
  intro _ hIncomplete
  exact incomplete_theorem_flow_not_theorem hIncomplete

theorem same_statement_multiple_flows :
    exists R : GeneratedTheoremRecognizer,
      exists statement T U : TheoremCandidateFlow,
        Not (T = U) /\
          TheoremRoleSubflow R T statement TheoremRole.statement /\
          TheoremRoleSubflow R U statement TheoremRole.statement := by
  refine
    ⟨[],
      [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b1]], ?_⟩
  constructor
  · intro h
    cases h
  · constructor
    · constructor
      · constructor
        · exact FormalCompilerInput.recognizedFlow []
            [[BEDC.FKernel.Mark.BMark.b0]]
        · exact ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩
      · exact ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩
    · constructor
      · constructor
        · exact FormalCompilerInput.recognizedFlow []
            [[BEDC.FKernel.Mark.BMark.b1]]
        · exact ⟨[BEDC.FKernel.Mark.BMark.b1], [], rfl⟩
      · exact ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩

theorem code_equality_refines_statement_equivalence
    {T U : TheoremCandidateFlow} :
    TheoremCode T = TheoremCode U -> T = U :=
  theorem_code_injective

def TheoremClassifierRelation : Type :=
  TheoremCandidateFlow -> TheoremCandidateFlow -> Prop

def TheoremClassifierQuotient
    (rel : TheoremClassifierRelation) (T U : TheoremCandidateFlow) : Prop :=
  rel T U

def ClassifierCollapsesDistinctTheoremCode
    (rel : TheoremClassifierRelation) : Prop :=
  exists T U : TheoremCandidateFlow,
    TheoremFlow T /\
      TheoremFlow U /\
      Not (TheoremCode T = TheoremCode U) /\
      TheoremClassifierQuotient rel T U

theorem classified_theorem_objects_not_code_bijective
    {rel : TheoremClassifierRelation} :
    (exists T U : TheoremCandidateFlow,
      TheoremFlow T /\
        TheoremFlow U /\
        Not (T = U) /\
        TheoremClassifierQuotient rel T U) ->
      ClassifierCollapsesDistinctTheoremCode rel := by
  intro h
  cases h with
  | intro T hT =>
      cases hT with
      | intro U hU =>
          refine ⟨T, U, hU.left, hU.right.left, ?_, hU.right.right.right⟩
          intro hCode
          exact hU.right.right.left (theorem_code_injective hCode)

theorem theorem_flow_object_layer_differ {rel : TheoremClassifierRelation} :
    (forall T U : TheoremCandidateFlow, TheoremCode T = TheoremCode U -> T = U) /\
      ((exists T U : TheoremCandidateFlow,
        TheoremFlow T /\
          TheoremFlow U /\
          Not (T = U) /\
          TheoremClassifierQuotient rel T U) ->
        ClassifierCollapsesDistinctTheoremCode rel) := by
  constructor
  · intro T U hCode
    exact theorem_code_injective hCode
  · intro h
    exact classified_theorem_objects_not_code_bijective h

end BEDC.GroundCompiler.TheoremGenerated
