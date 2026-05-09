import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.NameCertGenerated

namespace BEDC.GroundCompiler.DerivCertGenerated

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.NameCertGenerated

def GeneratedDerivCertRecognizer : Type :=
  GeneratedRecognizer

def P6GeneratedDerivCertRecognizer : Type :=
  GeneratedDerivCertRecognizer

def GeneratedAcceptGateRecognizer : Type :=
  GeneratedRecognizer

def GeneratedStrengthRecognizerFlow : Type :=
  EventFlow

inductive P6FormalInput : Type where
  | channel (c : List DisplayAlphabet) (h : LegalZStream c)
  | eventFlow (S : EventFlow)

inductive P6ExternalInput : Type where
  | acceptedObject
  | derivCertStruct
  | acceptGateStruct
  | strengthEnum

inductive P6InputRepresentation : Type where
  | formal (x : P6FormalInput)
  | external (x : P6ExternalInput)

inductive P6ReportDatum : Type where
  | decodedEventFlow (S : EventFlow)
  | recognizedNameCert (C N : EventFlow)
  | derivCertCandidate (D N s : EventFlow)
  | recognizedDerivCert
      (R : GeneratedDerivCertRecognizer) (D N s : EventFlow)
  | strengthCandidate (ambient s : EventFlow)
  | recognizedStrength
      (R : GeneratedStrengthRecognizer) (ambient s : EventFlow)
      (sigma : StrengthRole)
  | acceptGateCandidate (A N s : EventFlow)
  | recognizedAcceptGate
      (R : GeneratedAcceptGateRecognizer) (A N s : EventFlow)
  | acceptedObjectCode (A N s : EventFlow)
  | missingField (candidate : EventFlow)
  | warning (datum : EventFlow)
  | cannotClaim (datum : EventFlow)

def P6Output : Type :=
  List P6ReportDatum

theorem p6_external_inputs_not_formal :
    (forall x : P6FormalInput,
      Not (P6InputRepresentation.external P6ExternalInput.acceptedObject =
        P6InputRepresentation.formal x)) /\
      (forall x : P6FormalInput,
        Not (P6InputRepresentation.external P6ExternalInput.derivCertStruct =
          P6InputRepresentation.formal x)) /\
      (forall x : P6FormalInput,
        Not (P6InputRepresentation.external P6ExternalInput.acceptGateStruct =
          P6InputRepresentation.formal x)) := by
  constructor
  · intro x h
    cases h
  constructor
  · intro x h
    cases h
  · intro x h
    cases h

theorem no_strength_enum_input :
    forall x : P6FormalInput,
      Not (P6InputRepresentation.external P6ExternalInput.strengthEnum =
        P6InputRepresentation.formal x) := by
  intro x h
  cases h

def DerivCertSourceSubflow (part whole : EventFlow) : Prop :=
  exists before after : EventFlow, whole = List.append before (List.append part after)

def StrengthCandidateFlow (S s : EventFlow) : Prop :=
  DerivCertSourceSubflow s S

def P6DerivCertCandidate (S D N s : EventFlow) : Prop :=
  DerivCertSourceSubflow D S /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    StrengthCandidateFlow S s

def StrengthOrderWitness
    (R : GeneratedStrengthRecognizerFlow) (S o : EventFlow) : Prop :=
  DerivCertSourceSubflow o S /\
    FormalCompilerInput (CompilerDatum.recognizedFlow R o) /\
    StrengthRoleLT StrengthRole.seed StrengthRole.paperCert /\
    StrengthRoleLT StrengthRole.paperCert StrengthRole.checkedCert /\
    StrengthRoleLT StrengthRole.checkedCert StrengthRole.bridgeCert

def RecognizedStrengthFlow
    (R : GeneratedStrengthRecognizer) (S s : EventFlow)
    (sigma : StrengthRole) : Prop :=
  StrengthCandidateFlow S s /\ RecognizesStrength R s sigma

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

def P6CompleteDerivCertRecognition
    (R : P6GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow) : Prop :=
  CompleteSixFieldDerivCertRecognition R D

def P6DerivCertFieldSubflows
    (R : P6GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow) : Prop :=
  P6CompleteDerivCertRecognition R D

def RecognizesDerivCert
    (R : GeneratedDerivCertRecognizer) (D N s : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R D) /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    StrengthEventFlow s /\
    CompleteSixFieldDerivCertRecognition R D

def DerivCertFlow (D N s : EventFlow) : Prop :=
  exists R : GeneratedDerivCertRecognizer, RecognizesDerivCert R D N s

def P6RecognizedDerivCertFlow
    (R : GeneratedDerivCertRecognizer) (S D N s : EventFlow) : Prop :=
  P6DerivCertCandidate S D N s /\ RecognizesDerivCert R D N s

def AcceptGateCandidate (S A N s : EventFlow) : Prop :=
  DerivCertSourceSubflow A S /\
    FormalCompilerInput (CompilerDatum.eventFlow N) /\
    StrengthEventFlow s /\
    exists C D : EventFlow, DerivCertSourceSubflow C A /\ DerivCertSourceSubflow D A

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

def RecognizesAcceptGate
    (R : GeneratedAcceptGateRecognizer) (_S A N s : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R A) /\
    AcceptedFlow A N s

def P6RecognizedAcceptGateFlow
    (R : GeneratedAcceptGateRecognizer) (S A N s : EventFlow) : Prop :=
  AcceptGateCandidate S A N s /\ RecognizesAcceptGate R S A N s

def AcceptGateComponents
    (R : GeneratedAcceptGateRecognizer) (S A N s C D sealFlow : EventFlow) :
    Prop :=
  P6RecognizedAcceptGateFlow R S A N s /\
    NameCertFlow C N /\
    DerivCertFlow D N s /\
    StrengthEventFlow s /\
    DerivCertSourceSubflow C A /\
    DerivCertSourceSubflow D A /\
    DerivCertSourceSubflow sealFlow A

def AcceptGateFlow (N s : EventFlow) : Prop :=
  exists A : EventFlow, AcceptedFlow A N s

structure DerivAcceptPrototype where
  run : P6FormalInput -> P6Output
  externalInputsNotFormal :
    (forall x : P6FormalInput,
      Not (P6InputRepresentation.external P6ExternalInput.acceptedObject =
        P6InputRepresentation.formal x)) /\
      (forall x : P6FormalInput,
        Not (P6InputRepresentation.external P6ExternalInput.derivCertStruct =
          P6InputRepresentation.formal x)) /\
      (forall x : P6FormalInput,
        Not (P6InputRepresentation.external P6ExternalInput.acceptGateStruct =
          P6InputRepresentation.formal x))
  strengthEnumNotFormal :
    forall x : P6FormalInput,
      Not (P6InputRepresentation.external P6ExternalInput.strengthEnum =
        P6InputRepresentation.formal x)
  acceptedCodeMediated :
    forall {R : GeneratedAcceptGateRecognizer} {S A N s : EventFlow},
      P6RecognizedAcceptGateFlow R S A N s ->
        exists C D : EventFlow, NameCertFlow C N /\ DerivCertFlow D N s

def AcceptedObjectCode (A _N _s : EventFlow) : List DisplayAlphabet :=
  FlowEncoding A

def P6AcceptedObjectFlow (A N s : EventFlow) : Prop :=
  AcceptedFlow A N s

def P6AcceptedObjectCode (A N s : EventFlow) : List DisplayAlphabet :=
  AcceptedObjectCode A N s

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

def ClassifierObjectSame (A B : EventFlow) : Prop :=
  erase A = erase B

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

def P6DerivCertFieldSoundness
    (R : P6GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (N s source classifier exactness ledger stability strength : EventFlow) :
    Prop :=
  DerivCertFieldSoundness R D N s source classifier exactness ledger stability
    strength

def SoundRecognizedDerivCertFlow
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (N s : EventFlow) : Prop :=
  RecognizesDerivCert R D N s /\
    exists source classifier exactness ledger stability strength : EventFlow,
      DerivCertFieldSoundness R D N s source classifier exactness ledger
        stability strength

def P6SoundDerivCertFlow
    (R : GeneratedDerivCertRecognizer) (D : DerivCertCandidateFlow)
    (N s : EventFlow) : Prop :=
  SoundRecognizedDerivCertFlow R D N s

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

theorem p6_recognized_derivcert_has_six_fields
    {R : GeneratedDerivCertRecognizer} {S D N s : EventFlow} :
    P6RecognizedDerivCertFlow R S D N s ->
      CompleteSixFieldDerivCertRecognition R D := by
  intro h
  exact no_derivcert_without_six_fields h.right

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

theorem p6_incomplete_derivcert_candidate_no_export
    {D : DerivCertCandidateFlow} {N s : EventFlow} :
    (forall R : P6GeneratedDerivCertRecognizer,
      RecognizesDerivCert R D N s ->
        Not (P6CompleteDerivCertRecognition R D)) ->
      Not (DerivCertFlow D N s) := by
  intro hIncomplete
  exact incomplete_derivcert_does_not_support_export hIncomplete

theorem strength_flow_alone_insufficient
    {D : DerivCertCandidateFlow} {N s : EventFlow} :
    StrengthEventFlow s ->
      (forall R : GeneratedDerivCertRecognizer,
        RecognizesDerivCert R D N s ->
          Not (CompleteSixFieldDerivCertRecognition R D)) ->
        Not (DerivCertFlow D N s) := by
  intro _ hIncomplete
  exact incomplete_derivcert_does_not_support_export hIncomplete

theorem strength_candidate_without_recognition_insufficient
    {S s D N : EventFlow} :
    StrengthCandidateFlow S s ->
      (forall R : GeneratedStrengthRecognizer, forall sigma : StrengthRole,
        Not (RecognizesStrength R s sigma)) ->
        Not (DerivCertFlow D N s) := by
  intro _ hNoRecognition hFlow
  cases hFlow with
  | intro _ hRecognizes =>
      cases hRecognizes.right.right.left with
      | intro R hSigma =>
          cases hSigma with
          | intro sigma hStrength =>
              exact hNoRecognition R sigma hStrength

theorem p6_strength_alone_no_export
    {D : DerivCertCandidateFlow} {N s : EventFlow} :
    StrengthEventFlow s ->
      (forall R : P6GeneratedDerivCertRecognizer,
        RecognizesDerivCert R D N s ->
          Not (P6CompleteDerivCertRecognition R D)) ->
        Not (DerivCertFlow D N s) := by
  intro hStrength hIncomplete
  exact strength_flow_alone_insufficient hStrength hIncomplete

theorem sound_derivcert_recognition_establishes_flow
    {R : GeneratedDerivCertRecognizer} {D : DerivCertCandidateFlow}
    {N s : EventFlow} :
    SoundRecognizedDerivCertFlow R D N s -> DerivCertFlow D N s := by
  intro hSound
  exact ⟨R, hSound.left⟩

theorem p6_sound_derivcert_flow_establishes_derivcert
    {R : GeneratedDerivCertRecognizer} {D : DerivCertCandidateFlow}
    {N s : EventFlow} :
    P6SoundDerivCertFlow R D N s -> DerivCertFlow D N s := by
  intro hSound
  exact sound_derivcert_recognition_establishes_flow hSound

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

theorem p6_acceptgate_requires_namecert_derivcert
    {R : GeneratedAcceptGateRecognizer} {S A N s : EventFlow} :
    P6RecognizedAcceptGateFlow R S A N s ->
      exists C D : EventFlow, NameCertFlow C N /\ DerivCertFlow D N s := by
  intro hGate
  exact accepted_requires_namecert_derivcert ⟨A, hGate.right.right⟩

theorem p6_acceptgate_components_from_recognition
    {R : GeneratedAcceptGateRecognizer} {S A N s : EventFlow} :
    P6RecognizedAcceptGateFlow R S A N s ->
      exists C D sealFlow : EventFlow,
        AcceptGateComponents R S A N s C D sealFlow := by
  intro hGate
  cases hGate.right.right with
  | intro C hAccepted =>
      cases hAccepted with
      | intro D hAccepted =>
          cases hAccepted with
          | intro sealFlow hFields =>
              have hStrength : StrengthEventFlow s := by
                cases hFields.right.left with
                | intro _ hRecognizes =>
                    exact hRecognizes.right.right.left
              exact
                ⟨C, D, sealFlow, hGate, hFields.left, hFields.right.left,
                  hStrength, hFields.right.right.right.right.right.left,
                  hFields.right.right.right.right.right.right.left,
                  hFields.right.right.right.right.right.right.right⟩

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

theorem p6_accepted_object_code_injective_raw_flows
    {A B N M s t : EventFlow} :
    P6AcceptedObjectCode A N s = P6AcceptedObjectCode B M t -> A = B := by
  intro h
  exact accepted_object_code_injective h

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

theorem p6_strength_monotonicity : StrengthMonotonicityAtFlowLevel :=
  gate_monotone_strength

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

theorem no_retroactive_promotion {M oldStrength newStrength : EventFlow} :
    RetroactivePromotion M oldStrength newStrength ->
      Not (AcceptGateFlow M newStrength) := by
  intro hPromotion
  exact hPromotion.right

theorem accepted_flow_recognition_conservativity
    {A N s : EventFlow} {w : RawEvent} {m : DisplayAlphabet} :
    AcceptedFlow A N s -> List.Mem w A -> List.Mem m w ->
      m = BMark.b0 \/ m = BMark.b1 := by
  intro _ _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

theorem source_subflow_self (S : EventFlow) : SourceSubflow S S := by
  let rec appendNilRight : (xs : EventFlow) -> xs = [].append (List.append xs [])
    | [] => rfl
    | w :: rest => congrArg (List.cons w) (appendNilRight rest)
  exact ⟨[], [], appendNilRight S⟩

theorem derivcert_source_subflow_self (S : EventFlow) :
    DerivCertSourceSubflow S S := by
  let rec appendNilRight : (xs : EventFlow) -> xs = [].append (List.append xs [])
    | [] => rfl
    | w :: rest => congrArg (List.cons w) (appendNilRight rest)
  exact ⟨[], [], appendNilRight S⟩

theorem singleton_flow_nonempty (w : RawEvent) :
    NonemptyEventFlow [w] := by
  exact ⟨w, [], rfl⟩

theorem namecert_flow_self (C N : EventFlow) : NameCertFlow C N := by
  refine ⟨[], ?_⟩
  constructor
  · exact FormalCompilerInput.recognizedFlow [] C
  constructor
  · exact FormalCompilerInput.eventFlow N
  · refine ⟨C, C, C, C, C, C, ?_⟩
    constructor
    · exact ⟨FormalCompilerInput.recognizedFlow [] C, source_subflow_self C⟩
    constructor
    · exact ⟨FormalCompilerInput.recognizedFlow [] C, source_subflow_self C⟩
    constructor
    · exact ⟨FormalCompilerInput.recognizedFlow [] C, source_subflow_self C⟩
    constructor
    · exact ⟨FormalCompilerInput.recognizedFlow [] C, source_subflow_self C⟩
    constructor
    · exact ⟨FormalCompilerInput.recognizedFlow [] C, source_subflow_self C⟩
    · exact ⟨FormalCompilerInput.recognizedFlow [] C, source_subflow_self C⟩

theorem strength_event_flow_self (s : EventFlow) : StrengthEventFlow s := by
  exact ⟨[], StrengthRole.seed, FormalCompilerInput.recognizedFlow [] s⟩

theorem derivcert_flow_self (D N s : EventFlow) : DerivCertFlow D N s := by
  refine ⟨[], ?_⟩
  constructor
  · exact FormalCompilerInput.recognizedFlow [] D
  constructor
  · exact FormalCompilerInput.eventFlow N
  constructor
  · exact strength_event_flow_self s
  · refine ⟨D, D, D, D, D, D, D, ?_⟩
    constructor
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩
    constructor
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩
    constructor
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩
    constructor
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩
    constructor
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩
    constructor
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩
    · exact
        ⟨FormalCompilerInput.recognizedFlow [] D,
          derivcert_source_subflow_self D⟩

theorem accepted_flow_from_components
    {A C D sealFlow N s : EventFlow}
    (hC : NonemptyEventFlow C) (hD : NonemptyEventFlow D)
    (hSeal : NonemptyEventFlow sealFlow)
    (hCSub : DerivCertSourceSubflow C A)
    (hDSub : DerivCertSourceSubflow D A)
    (hSealSub : DerivCertSourceSubflow sealFlow A) :
    AcceptedFlow A N s := by
  exact
    ⟨C, D, sealFlow, namecert_flow_self C N, derivcert_flow_self D N s,
      hC, hD, hSeal, hCSub, hDSub, hSealSub⟩

theorem accepted_object_code_weaker_than_object_equality :
    exists A B N M s t : EventFlow,
      AcceptedFlow A N s /\
        AcceptedFlow B M t /\
        ClassifierObjectSame A B /\
        Not (A = B) := by
  refine
    ⟨[[BMark.b0], [BMark.b1], [BMark.b0, BMark.b1]],
      [[BMark.b0, BMark.b1], [BMark.b0], [BMark.b1]],
      [], [], [], [], ?_⟩
  constructor
  · exact
      accepted_flow_from_components
        (singleton_flow_nonempty [BMark.b0])
        (singleton_flow_nonempty [BMark.b1])
        (singleton_flow_nonempty [BMark.b0, BMark.b1])
        ⟨[], [[BMark.b1], [BMark.b0, BMark.b1]], rfl⟩
        ⟨[[BMark.b0]], [[BMark.b0, BMark.b1]], rfl⟩
        ⟨[[BMark.b0], [BMark.b1]], [], rfl⟩
  constructor
  · exact
      accepted_flow_from_components
        (singleton_flow_nonempty [BMark.b0, BMark.b1])
        (singleton_flow_nonempty [BMark.b0])
        (singleton_flow_nonempty [BMark.b1])
        ⟨[], [[BMark.b0], [BMark.b1]], rfl⟩
        ⟨[[BMark.b0, BMark.b1]], [[BMark.b1]], rfl⟩
        ⟨[[BMark.b0, BMark.b1], [BMark.b0]], [], rfl⟩
  constructor
  · rfl
  · intro hEqual
    cases hEqual

theorem p6_accepted_code_equality_stronger_than_equivalence :
    exists A B N M s t : EventFlow,
      AcceptedFlow A N s /\
        AcceptedFlow B M t /\
        ClassifierObjectSame A B /\
        Not (A = B) :=
  accepted_object_code_weaker_than_object_equality

end BEDC.GroundCompiler.DerivCertGenerated
