import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.NameCertGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def NameCandidateFlow : Type :=
  EventFlow

def NameCertCandidateFlow : Type :=
  EventFlow

def GeneratedNameCertRecognizer : Type :=
  GeneratedRecognizer

def SourceSubflow (part whole : EventFlow) : Prop :=
  exists before after : EventFlow, whole = List.append before (List.append part after)

inductive NameCertFieldRole : Type where
  | source
  | pattern
  | classifier
  | stability
  | ledger

def NameCertFieldSubflow
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (_role : NameCertFieldRole) (part : EventFlow) : Prop :=
  RecognizesNameCert R S /\ SourceSubflow part S

def NameCertSealSubflow
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (sealFlow : EventFlow) : Prop :=
  RecognizesNameCert R S /\ SourceSubflow sealFlow S

def CompleteFiveFieldRecognition
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow) : Prop :=
  exists source pattern classifier stability ledger sealFlow : EventFlow,
    NameCertFieldSubflow R S NameCertFieldRole.source source /\
      NameCertFieldSubflow R S NameCertFieldRole.pattern pattern /\
      NameCertFieldSubflow R S NameCertFieldRole.classifier classifier /\
      NameCertFieldSubflow R S NameCertFieldRole.stability stability /\
      NameCertFieldSubflow R S NameCertFieldRole.ledger ledger /\
      NameCertSealSubflow R S sealFlow

def NameCertRecognitionRelation
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (N : NameCandidateFlow) : Prop :=
  RecognizesNameCert R S /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    CompleteFiveFieldRecognition R S

def NameCertFlow (S : NameCertCandidateFlow) (N : NameCandidateFlow) : Prop :=
  exists R : GeneratedNameCertRecognizer, NameCertRecognitionRelation R S N

def LicensedName (N : NameCandidateFlow) : Prop :=
  exists S : NameCertCandidateFlow, NameCertFlow S N

def LedgerCompleteNameCertFlow
    (S : NameCertCandidateFlow) (N : NameCandidateFlow) : Prop :=
  exists R : GeneratedNameCertRecognizer,
    exists ledger : EventFlow,
      NameCertRecognitionRelation R S N /\
        NameCertFieldSubflow R S NameCertFieldRole.ledger ledger

def NameCertSoundnessEvent
    (_R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (part : EventFlow) : Prop :=
  SourceSubflow part S

def NameCertSourceSoundnessEvent
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (part : EventFlow) : Prop :=
  NameCertSoundnessEvent R S part

def NameCertPatternSoundnessEvent
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (part : EventFlow) : Prop :=
  NameCertFieldSubflow R S NameCertFieldRole.pattern part /\
    NameCertSoundnessEvent R S part

def NameCertClassifierSoundnessEvent
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (part : EventFlow) : Prop :=
  NameCertFieldSubflow R S NameCertFieldRole.classifier part /\
    NameCertSoundnessEvent R S part

def NameCertStabilitySoundnessEvent
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (part : EventFlow) : Prop :=
  NameCertFieldSubflow R S NameCertFieldRole.stability part /\
    NameCertSoundnessEvent R S part

def NameCertLedgerSoundnessEvent
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (part : EventFlow) : Prop :=
  NameCertFieldSubflow R S NameCertFieldRole.ledger part /\
    NameCertSoundnessEvent R S part

def SoundRecognizedNameCertFlow
    (R : GeneratedNameCertRecognizer) (S : NameCertCandidateFlow)
    (N : NameCandidateFlow) : Prop :=
  NameCertRecognitionRelation R S N /\
    exists source pattern classifier stability ledger : EventFlow,
      NameCertFieldSubflow R S NameCertFieldRole.source source /\
        NameCertSoundnessEvent R S source /\
        NameCertFieldSubflow R S NameCertFieldRole.pattern pattern /\
        NameCertSoundnessEvent R S pattern /\
        NameCertFieldSubflow R S NameCertFieldRole.classifier classifier /\
        NameCertSoundnessEvent R S classifier /\
        NameCertFieldSubflow R S NameCertFieldRole.stability stability /\
        NameCertSoundnessEvent R S stability /\
        NameCertFieldSubflow R S NameCertFieldRole.ledger ledger /\
        NameCertSoundnessEvent R S ledger

def NameCertCode (S : NameCertCandidateFlow) (_N : NameCandidateFlow) :
    List DisplayAlphabet :=
  FlowEncoding S

def RecognizesNameCertCode
    (R : GeneratedNameCertRecognizer) (c : List DisplayAlphabet)
    (N : NameCandidateFlow) : Prop :=
  exists S : EventFlow,
    Decode c = some S /\ NameCertRecognitionRelation R S N

def NameCertRecognitionPreservingCompilation : Prop :=
  forall R : GeneratedNameCertRecognizer,
    forall S : NameCertCandidateFlow,
    forall N : NameCandidateFlow,
      NameCertRecognitionRelation R S N ->
        exists S' : EventFlow,
          Decode (FlowEncoding S) = some S' /\
            NameCertRecognitionRelation R S' N

theorem no_external_namecert_input :
    Not (FormalCompilerInput CompilerDatum.hostNameCert) :=
  structural_hidden_not_formal StructuralHiddenInput.hostNameCert

theorem no_namecert_without_five_fields
    {R : GeneratedNameCertRecognizer} {S : NameCertCandidateFlow}
    {N : NameCandidateFlow} :
    NameCertRecognitionRelation R S N -> CompleteFiveFieldRecognition R S := by
  intro h
  exact h.right.right

theorem incomplete_namecert_does_not_license
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} :
    (forall R : GeneratedNameCertRecognizer,
      NameCertRecognitionRelation R S N ->
        Not (CompleteFiveFieldRecognition R S)) ->
      Not (NameCertFlow S N) := by
  intro hIncomplete hFlow
  cases hFlow with
  | intro R hRecognizes =>
      exact hIncomplete R hRecognizes hRecognizes.right.right

theorem namecert_seal_is_source_subflow
    {R : GeneratedNameCertRecognizer} {S : NameCertCandidateFlow}
    {sealFlow : EventFlow} :
    NameCertSealSubflow R S sealFlow -> SourceSubflow sealFlow S := by
  intro hSeal
  exact hSeal.right

theorem namecert_without_ledger_not_admissible
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} :
    (forall R : GeneratedNameCertRecognizer,
      forall ledger : EventFlow,
        NameCertRecognitionRelation R S N ->
          Not (NameCertFieldSubflow R S NameCertFieldRole.ledger ledger)) ->
      Not (NameCertFlow S N) := by
  intro hNoLedger hFlow
  cases hFlow with
  | intro R hRecognizes =>
      cases hRecognizes.right.right with
      | intro source hComplete =>
          cases hComplete with
          | intro pattern hComplete =>
              cases hComplete with
              | intro classifier hComplete =>
                  cases hComplete with
                  | intro stability hComplete =>
                      cases hComplete with
                      | intro ledger hComplete =>
                          cases hComplete with
                          | intro sealFlow hFields =>
                              exact hNoLedger R ledger hRecognizes
                                hFields.right.right.right.right.left

theorem certified_derived_carry_ledger
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} :
    NameCertFlow S N -> LedgerCompleteNameCertFlow S N := by
  intro hFlow
  cases hFlow with
  | intro R hRecognizes =>
      cases hRecognizes.right.right with
      | intro source hComplete =>
          cases hComplete with
          | intro pattern hComplete =>
              cases hComplete with
              | intro classifier hComplete =>
                  cases hComplete with
                  | intro stability hComplete =>
                      cases hComplete with
                      | intro ledger hComplete =>
                          cases hComplete with
                          | intro sealFlow hFields =>
                              exact
                                ⟨R, ledger, hRecognizes,
                                  hFields.right.right.right.right.left⟩

theorem four_fields_without_ledger_not_enough
    {R : GeneratedNameCertRecognizer} {S : NameCertCandidateFlow}
    {source pattern classifier stability : EventFlow} :
    NameCertFieldSubflow R S NameCertFieldRole.source source ->
      NameCertFieldSubflow R S NameCertFieldRole.pattern pattern ->
        NameCertFieldSubflow R S NameCertFieldRole.classifier classifier ->
          NameCertFieldSubflow R S NameCertFieldRole.stability stability ->
            (forall ledger : EventFlow,
              Not (NameCertFieldSubflow R S NameCertFieldRole.ledger ledger)) ->
              Not (CompleteFiveFieldRecognition R S) := by
  intro _ _ _ _ hNoLedger hComplete
  cases hComplete with
  | intro completeSource hComplete =>
      cases hComplete with
      | intro completePattern hComplete =>
          cases hComplete with
          | intro completeClassifier hComplete =>
              cases hComplete with
              | intro completeStability hComplete =>
                  cases hComplete with
                  | intro ledger hComplete =>
                      cases hComplete with
                      | intro sealFlow hFields =>
                          exact hNoLedger ledger
                            hFields.right.right.right.right.left

theorem namecert_recognition_preserves_code
    {R : GeneratedNameCertRecognizer} {S : NameCertCandidateFlow}
    {N : NameCandidateFlow} :
    NameCertRecognitionRelation R S N ->
      LegalZStream (FlowEncoding S) /\ Decode (FlowEncoding S) = some S := by
  intro _
  exact ⟨flow_encoding_legal_zstream S, flow_level_round_trip S⟩

theorem namecert_code_not_separate
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} :
    NameCertFlow S N ->
      LegalZStream (NameCertCode S N) /\ Decode (NameCertCode S N) = some S := by
  intro _
  exact ⟨flow_encoding_legal_zstream S, flow_level_round_trip S⟩

theorem namecert_recognition_invariant
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} :
    NameCertFlow S N ->
      exists S' : EventFlow,
        Decode (NameCertCode S N) = some S' /\ NameCertFlow S' N := by
  intro hFlow
  exact ⟨S, flow_level_round_trip S, hFlow⟩

theorem licensing_event_flow_based {N : NameCandidateFlow} :
    LicensedName N -> exists S : EventFlow, NameCertFlow S N := by
  intro h
  exact h

theorem visible_name_event_insufficient {N : NameCandidateFlow} :
    FormalCompilerInput (CompilerDatum.eventFlow N) ->
      (forall S : NameCertCandidateFlow, Not (NameCertFlow S N)) ->
      Not (LicensedName N) := by
  intro _ hNoFlow hLicensed
  cases hLicensed with
  | intro S hFlow =>
      exact hNoFlow S hFlow

theorem derived_interfaces_require_flow {N : NameCandidateFlow} :
    LicensedName N -> exists S : EventFlow, NameCertFlow S N := by
  intro h
  exact h

theorem no_upward_from_raw_code_alone
    {c : List DisplayAlphabet} {N : NameCandidateFlow} :
    (exists R : GeneratedNameCertRecognizer, RecognizesNameCertCode R c N) ->
      exists S : EventFlow, Decode c = some S /\ NameCertFlow S N := by
  intro hCode
  cases hCode with
  | intro R hRecognizesCode =>
      cases hRecognizesCode with
      | intro S hDecoded =>
          exact ⟨S, hDecoded.left, R, hDecoded.right⟩

theorem namecert_code_injective
    {S T : NameCertCandidateFlow} {N M : NameCandidateFlow} :
    NameCertFlow S N ->
      NameCertFlow T M ->
        NameCertCode S N = NameCertCode T M -> S = T := by
  intro _ _ hCode
  have hDecode : Decode (NameCertCode S N) = Decode (NameCertCode T M) := by
    rw [hCode]
  rw [NameCertCode, NameCertCode, flow_level_round_trip S,
    flow_level_round_trip T] at hDecode
  cases hDecode
  rfl

theorem channel_compilation_preserves_namecert_recognition :
    NameCertRecognitionPreservingCompilation := by
  intro R S N hRecognizes
  exact ⟨S, flow_level_round_trip S, hRecognizes⟩

theorem no_namecert_recognition_by_channel_substring
    {R : GeneratedNameCertRecognizer} {c : List DisplayAlphabet}
    {N : NameCandidateFlow} :
    RecognizesNameCertCode R c N ->
      exists S : EventFlow,
        Decode c = some S /\ NameCertRecognitionRelation R S N := by
  intro h
  exact h

theorem sound_namecert_flow_licenses_name
    {R : GeneratedNameCertRecognizer} {S : NameCertCandidateFlow}
    {N : NameCandidateFlow} :
    SoundRecognizedNameCertFlow R S N -> LicensedName N := by
  intro hSound
  exact ⟨S, R, hSound.left⟩

theorem namecert_flow_recognition_conservativity
    {S : NameCertCandidateFlow} {N : NameCandidateFlow} {w : RawEvent}
    {m : DisplayAlphabet} :
    NameCertFlow S N -> List.Mem w S -> List.Mem m w ->
      m = BEDC.FKernel.Mark.BMark.b0 \/ m = BEDC.FKernel.Mark.BMark.b1 := by
  intro _ hw hm
  exact event_flow_conservativity hw hm

end BEDC.GroundCompiler.NameCertGenerated
