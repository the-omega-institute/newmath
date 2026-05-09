import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.NameCertGenerated

namespace BEDC.GroundCompiler.DerivCertGenerated

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.NameCertGenerated

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

def AcceptedFlow (A N s : EventFlow) : Prop :=
  exists C D sealFlow : EventFlow,
    NameCertFlow C N /\
      DerivCertFlow D N s /\
      NonemptyEventFlow C /\
      NonemptyEventFlow D /\
      NonemptyEventFlow sealFlow /\
      DerivCertSourceSubflow C A /\
      DerivCertSourceSubflow D A /\
      DerivCertSourceSubflow sealFlow A

def AcceptGateFlow (N s : EventFlow) : Prop :=
  exists A : EventFlow, AcceptedFlow A N s

def AcceptedObjectCode (A _N _s : EventFlow) : List DisplayAlphabet :=
  FlowEncoding A

def RecognizesAcceptanceCode
    (c : List DisplayAlphabet) (N s : EventFlow) : Prop :=
  exists A : EventFlow, Decode c = some A /\ AcceptedFlow A N s

def StrengthMonotonicityAtFlowLevel : Prop :=
  forall N high low A : EventFlow,
    AcceptedFlow A N high ->
      (exists Dlow : EventFlow,
        DerivCertFlow Dlow N low /\
          NonemptyEventFlow Dlow /\
          DerivCertSourceSubflow Dlow A) ->
        AcceptedFlow A N low

def ReuseFlow
    (U : EventFlow) (inputs : List (EventFlow × EventFlow))
    (M s : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow U) /\
    NonemptyEventFlow U /\
    (forall input : EventFlow × EventFlow,
      List.Mem input inputs -> AcceptGateFlow input.fst input.snd) /\
    exists A : EventFlow, AcceptedFlow A M s /\ DerivCertSourceSubflow U A

def RetroactivePromotion
    (M oldStrength newStrength : EventFlow) : Prop :=
  AcceptGateFlow M oldStrength /\ Not (AcceptGateFlow M newStrength)

def DerivCertCode (D _N _s : EventFlow) : List DisplayAlphabet :=
  FlowEncoding D

def DerivSourceSound
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (part N : EventFlow) : Prop :=
  DerivCertFieldSubflow R D DerivCertFieldRole.source part /\
    FormalCompilerInput (CompilerDatum.eventFlow N)

def DerivClassifierSound
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (part N : EventFlow) : Prop :=
  DerivCertFieldSubflow R D DerivCertFieldRole.classifier part /\
    FormalCompilerInput (CompilerDatum.eventFlow N)

def DerivExactnessSound
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (part N : EventFlow) : Prop :=
  DerivCertFieldSubflow R D DerivCertFieldRole.exactness part /\
    FormalCompilerInput (CompilerDatum.eventFlow N)

def DerivLedgerSound
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (part N : EventFlow) : Prop :=
  DerivCertFieldSubflow R D DerivCertFieldRole.ledger part /\
    FormalCompilerInput (CompilerDatum.eventFlow N)

def DerivStabilitySound
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (part N : EventFlow) : Prop :=
  DerivCertFieldSubflow R D DerivCertFieldRole.stability part /\
    FormalCompilerInput (CompilerDatum.eventFlow N)

def DerivStrengthSound
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (part s : EventFlow) : Prop :=
  DerivCertFieldSubflow R D DerivCertFieldRole.strength part /\
    StrengthEventFlow s

def DerivCertFieldSoundness
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (N s source classifier exactness ledger stability strength : EventFlow) :
    Prop :=
  DerivSourceSound R D source N /\
    DerivClassifierSound R D classifier N /\
    DerivExactnessSound R D exactness N /\
    DerivLedgerSound R D ledger N /\
    DerivStabilitySound R D stability N /\
    DerivStrengthSound R D strength s

def SoundRecognizedDerivCertFlow
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (N s : EventFlow) : Prop :=
  RecognizesDerivCert R D N s /\
    exists source classifier exactness ledger stability strength : EventFlow,
      DerivCertFieldSoundness R D N s source classifier exactness ledger
        stability strength

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

theorem derivcert_seal_is_source_subflow
    {R : GeneratedDerivCertRecognizer} {D : DerivCertCandidateFlow}
    {sealFlow : EventFlow} :
    DerivCertSealSubflow R D sealFlow ->
      DerivCertSourceSubflow sealFlow D := by
  intro hSeal
  exact hSeal.right

theorem incomplete_derivcert_does_not_support_export
    {D : DerivCertCandidateFlow} {N s : EventFlow} :
    (forall R : GeneratedDerivCertRecognizer,
      RecognizesDerivCert R D N s ->
        Not (CompleteSixFieldDerivCertRecognition R D)) ->
      Not (DerivCertFlow D N s) := by
  intro hIncomplete hFlow
  cases hFlow with
  | intro R hRecognizes =>
      exact hIncomplete R hRecognizes hRecognizes.right.right.right

theorem strength_flow_alone_insufficient
    {D : DerivCertCandidateFlow} {N s : EventFlow} :
    StrengthEventFlow s ->
      (forall R : GeneratedDerivCertRecognizer,
        RecognizesDerivCert R D N s ->
          Not (CompleteSixFieldDerivCertRecognition R D)) ->
        Not (DerivCertFlow D N s) := by
  intro _ hIncomplete
  exact incomplete_derivcert_does_not_support_export hIncomplete

theorem sound_derivcert_recognition_establishes_flow
    {R : GeneratedDerivCertRecognizer} {D : DerivCertCandidateFlow}
    {N s : EventFlow} :
    SoundRecognizedDerivCertFlow R D N s -> DerivCertFlow D N s := by
  intro hSound
  exact ⟨R, hSound.left⟩

theorem accepted_requires_namecert_derivcert {N s : EventFlow} :
    AcceptGateFlow N s ->
      exists C D : EventFlow, NameCertFlow C N /\ DerivCertFlow D N s := by
  intro hGate
  cases hGate with
  | intro A hAccepted =>
      cases hAccepted with
      | intro C hAccepted =>
          cases hAccepted with
          | intro D hAccepted =>
              cases hAccepted with
              | intro _ hAccepted =>
                  exact ⟨C, D, hAccepted.left, hAccepted.right.left⟩

theorem nonempty_not_derivcert_subflow_of_empty {part : EventFlow} :
    NonemptyEventFlow part -> Not (DerivCertSourceSubflow part []) := by
  intro hNonempty hSubflow
  cases hNonempty with
  | intro w hRest =>
      cases hRest with
      | intro rest hPart =>
          cases hSubflow with
          | intro before hAfter =>
              cases hAfter with
              | intro after hWhole =>
                  rw [hPart] at hWhole
                  cases before with
                  | nil =>
                      cases hWhole
                  | cons _ _ =>
                      cases hWhole

theorem empty_not_accepted_flow {N s : EventFlow} :
    Not (AcceptedFlow [] N s) := by
  intro hAccepted
  cases hAccepted with
  | intro C hAccepted =>
      cases hAccepted with
      | intro D hAccepted =>
          cases hAccepted with
          | intro sealFlow hFields =>
              exact
                nonempty_not_derivcert_subflow_of_empty
                  hFields.right.right.left
                  hFields.right.right.right.right.right.left

theorem code_existence_not_acceptance (N s : EventFlow) :
    LegalZStream [] /\ Not (RecognizesAcceptanceCode [] N s) := by
  constructor
  · exact flow_encoding_legal_zstream []
  · intro hRecognizes
    cases hRecognizes with
    | intro A hDecoded =>
        cases hDecoded with
        | intro hDecode hAccepted =>
            cases hDecode
            exact empty_not_accepted_flow hAccepted

theorem accepted_object_code_injective
    {A B N M s t : EventFlow} :
    AcceptedObjectCode A N s = AcceptedObjectCode B M t -> A = B := by
  intro h
  have hA : Decode (AcceptedObjectCode A N s) = some A := by
    simpa [AcceptedObjectCode] using flow_level_round_trip A
  have hB : Decode (AcceptedObjectCode B M t) = some B := by
    simpa [AcceptedObjectCode] using flow_level_round_trip B
  rw [h] at hA
  rw [hB] at hA
  cases hA
  rfl

theorem no_acceptance_recognition_by_channel_substring
    {c : List DisplayAlphabet} {N s : EventFlow} :
    RecognizesAcceptanceCode c N s ->
      exists A : EventFlow, Decode c = some A /\ AcceptedFlow A N s := by
  intro h
  exact h

theorem channel_compilation_preserves_acceptance
    {A N s : EventFlow} :
    AcceptedFlow A N s -> RecognizesAcceptanceCode (FlowEncoding A) N s := by
  intro hAccepted
  exact ⟨A, flow_level_round_trip A, hAccepted⟩

theorem acceptance_recognition_invariant {A N s : EventFlow} :
    AcceptedFlow A N s ->
      exists A' : EventFlow,
        Decode (FlowEncoding A) = some A' /\ A' = A /\ AcceptedFlow A' N s := by
  intro hAccepted
  exact ⟨A, flow_level_round_trip A, rfl, hAccepted⟩

theorem gate_monotone_strength : StrengthMonotonicityAtFlowLevel := by
  intro N high low A hAccepted hLower
  cases hAccepted with
  | intro C hAccepted =>
      cases hAccepted with
      | intro D hAccepted =>
          cases hAccepted with
          | intro sealFlow hAccepted =>
              cases hLower with
              | intro Dlow hLower =>
                  exact
                    ⟨C, Dlow, sealFlow, hAccepted.left, hLower.left,
                      hAccepted.right.right.left, hLower.right.left,
                      hAccepted.right.right.right.right.left,
                      hAccepted.right.right.right.right.right.left,
                      hLower.right.right,
                      hAccepted.right.right.right.right.right.right.right⟩

theorem reuse_closure_at_flow_level
    {U M s : EventFlow} {inputs : List (EventFlow × EventFlow)} :
    ReuseFlow U inputs M s -> AcceptGateFlow M s := by
  intro hReuse
  cases hReuse.right.right.right with
  | intro A hAccepted =>
      exact ⟨A, hAccepted.left⟩

theorem reuse_does_not_erase_obligations {M s : EventFlow} :
    AcceptGateFlow M s ->
      exists C D : EventFlow, NameCertFlow C M /\ DerivCertFlow D M s :=
  accepted_requires_namecert_derivcert

theorem accepted_flow_recognition_conservativity
    {A N s : EventFlow} {w : RawEvent} {m : DisplayAlphabet} :
    AcceptedFlow A N s -> List.Mem w A -> List.Mem m w ->
      m = BMark.b0 \/ m = BMark.b1 := by
  intro _ _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

end BEDC.GroundCompiler.DerivCertGenerated
