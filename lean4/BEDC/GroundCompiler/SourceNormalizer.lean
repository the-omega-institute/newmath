import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.SourceReport

namespace BEDC.GroundCompiler.SourceNormalizer

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.SourceReport

inductive AdjPair : EventFlow -> Nat -> RawEvent -> RawEvent -> Prop where
  | here (w v : RawEvent) (rest : EventFlow) :
      AdjPair (w :: v :: rest) 0 w v
  | there (x : RawEvent) {S : EventFlow} {i : Nat} {w v : RawEvent} :
      AdjPair S i w v -> AdjPair (x :: S) (i + 1) w v

def CandNormPair
    (candidate : RawEvent -> RawEvent -> Prop)
    (w v : RawEvent) : Prop :=
  candidate w v

def NormCand
    (candidate : RawEvent -> RawEvent -> Prop)
    (S : EventFlow) (i : Nat) (w v : RawEvent) : Prop :=
  AdjPair S i w v /\ CandNormPair candidate w v

def GeneratedNormalizerRecognizer : Type :=
  EventFlow

def RecognizesNormalizer
    (R : GeneratedNormalizerRecognizer) (S : EventFlow)
    (i : Nat) (w v : RawEvent) : Prop :=
  AdjPair S i w v /\ NonemptyEventFlow R

def NormLedger
    (R : GeneratedNormalizerRecognizer) (S : EventFlow)
    (i : Nat) (w v : RawEvent) : Prop :=
  RecognizesNormalizer R S i w v

def InducedNormalizes
    (R : GeneratedNormalizerRecognizer) (S : EventFlow)
    (i : Nat) (w v : RawEvent) : Prop :=
  NormLedger R S i w v

def PreNormalNormalAddressRoles
    (candidate : RawEvent -> RawEvent -> Prop)
    (R : GeneratedNormalizerRecognizer) (S : EventFlow)
    (i : Nat) (w v : RawEvent) : Prop :=
  NormCand candidate S i w v \/ NormLedger R S i w v

def CandidatePolicyFlow : Type :=
  EventFlow

def GeneratedCandidatePolicyRecognizer : Type :=
  EventFlow

def RecognizesCandidatePolicy
    (R : GeneratedCandidatePolicyRecognizer) (P : CandidatePolicyFlow) : Prop :=
  NonemptyEventFlow R /\ NonemptyEventFlow P

def CandidateMarkedByPolicy
    (R : GeneratedCandidatePolicyRecognizer) (P : CandidatePolicyFlow)
    (S : EventFlow) (i : Nat) (w v : RawEvent) : Prop :=
  RecognizesCandidatePolicy R P /\ AdjPair S i w v

def LiteralAdjacentPairListing
    (S : EventFlow) (i : Nat) (w v : RawEvent) : Prop :=
  AdjPair S i w v

structure NormalizerRecognizerCert where
  certFlow : EventFlow
  recognizer : GeneratedNormalizerRecognizer
  domainFlow : EventFlow
  candidatePolicyFlow : EventFlow
  preNormalCriterionFlow : EventFlow
  normalAddressCriterionFlow : EventFlow
  relationSoundnessFlow : EventFlow
  ledgerFlow : EventFlow
  failureFlow : EventFlow
  stabilityFlow : EventFlow
  sealFlow : EventFlow

def NormalizerSoundness (R : GeneratedNormalizerRecognizer) : Prop :=
  forall {S : EventFlow} {i : Nat} {w v : RawEvent},
    RecognizesNormalizer R S i w v -> InducedNormalizes R S i w v

def LedgerPreservingNormalizer (R : GeneratedNormalizerRecognizer) : Prop :=
  forall {S : EventFlow} {i : Nat} {w v : RawEvent},
    RecognizesNormalizer R S i w v ->
      NormLedger R S i w v /\ List.Mem w S /\ List.Mem v S

inductive P2Warning : Type where
  | candidateOnly
  | recognizerMissing
  | noCarryClaim
  | noChannelRewrite

inductive P2CannotClaim : Type where
  | rawEquality
  | hsame
  | theoremhood
  | nameCertificate
  | acceptedObject

structure P2Report where
  inputChannel : List DisplayAlphabet
  decodedFlow : EventFlow
  adjacentPairs : List (Nat × RawEvent × RawEvent)
  candidatePairs : List (Nat × RawEvent × RawEvent)
  recognizedLedgers :
    List (GeneratedNormalizerRecognizer × Nat × RawEvent × RawEvent)
  preNormalEvents : List RawEvent
  normalAddressEvents : List RawEvent
  candidateOnlyWarnings : List P2Warning
  roundTripStatus : Bool

structure P2ReportFormat where
  report : P2Report
  candidatePolicyRecognized : Bool
  cannotClaims : List P2CannotClaim

theorem adj_pair_events_mem {S : EventFlow} {i : Nat} {w v : RawEvent} :
    AdjPair S i w v -> List.Mem w S /\ List.Mem v S := by
  intro h
  induction h with
  | here w v rest =>
      constructor
      · exact List.Mem.head (v :: rest)
      · exact List.Mem.tail w (List.Mem.head rest)
  | there x h ih =>
      constructor
      · exact List.Mem.tail x ih.left
      · exact List.Mem.tail x ih.right

theorem candidate_preserves_raw
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v -> List.Mem w S /\ List.Mem v S := by
  intro h
  exact adj_pair_events_mem h.left

theorem candidate_does_not_erase_pre_normal
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v -> List.Mem w S := by
  intro h
  exact (candidate_preserves_raw h).left

theorem literal_listing_policy_free
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    AdjPair S i w v -> LiteralAdjacentPairListing S i w v := by
  intro h
  exact h

theorem no_hardcoded_table
    {R : GeneratedCandidatePolicyRecognizer} {P : CandidatePolicyFlow}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    Not (RecognizesCandidatePolicy R P) ->
      Not (CandidateMarkedByPolicy R P S i w v) := by
  intro hNoPolicy hMarked
  exact hNoPolicy hMarked.left

theorem candidate_marking_requires_policy
    {R : GeneratedCandidatePolicyRecognizer} {P : CandidatePolicyFlow}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    CandidateMarkedByPolicy R P S i w v ->
      RecognizesCandidatePolicy R P := by
  intro hMarked
  exact hMarked.left

theorem no_normalization_without_recognizer
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v ->
      (forall R : GeneratedNormalizerRecognizer, Not (NormLedger R S i w v)) ->
      Not (exists R : GeneratedNormalizerRecognizer, InducedNormalizes R S i w v) := by
  intro _ hNoRecognized hRelation
  cases hRelation with
  | intro R hInduced =>
      exact hNoRecognized R hInduced

theorem candidate_recognized_separated
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v ->
      (forall R : GeneratedNormalizerRecognizer,
        Not (RecognizesNormalizer R S i w v)) ->
      Not (exists R : GeneratedNormalizerRecognizer,
        InducedNormalizes R S i w v) := by
  intro hCand hNoRecognized
  exact no_normalization_without_recognizer hCand hNoRecognized

theorem candidate_not_relation
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v ->
      (forall R : GeneratedNormalizerRecognizer,
        Not (RecognizesNormalizer R S i w v)) ->
      Not (exists R : GeneratedNormalizerRecognizer,
        InducedNormalizes R S i w v) := by
  intro hCand hNoRecognized
  exact candidate_recognized_separated hCand hNoRecognized

def source011 : RawEvent :=
  [BMark.b0, BMark.b1, BMark.b1]

def source100 : RawEvent :=
  [BMark.b1, BMark.b0, BMark.b0]

def source011100Flow : EventFlow :=
  [source011, source100]

def Candidate011100 (w v : RawEvent) : Prop :=
  w = source011 /\ v = source100

theorem source011100_candidate :
    NormCand Candidate011100 source011100Flow 0 source011 source100 := by
  constructor
  · exact AdjPair.here source011 source100 []
  · constructor
    · rfl
    · rfl

theorem source011_100_not_carry
    (hNoRecognized :
      forall R : GeneratedNormalizerRecognizer,
        Not (RecognizesNormalizer R source011100Flow 0 source011 source100)) :
    Not (exists R : GeneratedNormalizerRecognizer,
      InducedNormalizes R source011100Flow 0 source011 source100) := by
  exact candidate_not_relation source011100_candidate hNoRecognized

theorem sound_recognizer_establishes_relation
    {R : GeneratedNormalizerRecognizer} {S : EventFlow}
    {i : Nat} {w v : RawEvent} :
    NormalizerSoundness R ->
      RecognizesNormalizer R S i w v -> InducedNormalizes R S i w v := by
  intro hSound hRecognized
  exact hSound hRecognized

theorem recognized_stronger_than_candidate
    {candidate : RawEvent -> RawEvent -> Prop}
    {R : GeneratedNormalizerRecognizer} {S : EventFlow}
    {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v ->
      NormalizerSoundness R ->
      RecognizesNormalizer R S i w v ->
      InducedNormalizes R S i w v /\ List.Mem w S /\ List.Mem v S := by
  intro _ hSound hRecognized
  constructor
  · exact hSound hRecognized
  · exact adj_pair_events_mem hRecognized.left

theorem recognized_normalizer_ledger_preserving
    (R : GeneratedNormalizerRecognizer) :
    LedgerPreservingNormalizer R := by
  intro S i w v hRecognized
  constructor
  · exact hRecognized
  · exact adj_pair_events_mem hRecognized.left

theorem ledger_preserving_no_collapse
    {R : GeneratedNormalizerRecognizer} {S : EventFlow}
    {i : Nat} {w v : RawEvent} :
    LedgerPreservingNormalizer R ->
      RecognizesNormalizer R S i w v -> List.Mem w S /\ List.Mem v S := by
  intro hLedger hRecognized
  exact (hLedger hRecognized).right

theorem recognized_normalizer_relation_source_level
    {R : GeneratedNormalizerRecognizer} {S : EventFlow}
    {i : Nat} {w v : RawEvent} :
    InducedNormalizes R S i w v -> AdjPair S i w v := by
  intro hRelation
  exact hRelation.left

theorem p2_candidate_report_conservative
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v ->
      (forall R : GeneratedNormalizerRecognizer,
        Not (RecognizesNormalizer R S i w v)) ->
      Not (exists R : GeneratedNormalizerRecognizer,
        InducedNormalizes R S i w v) := by
  intro hCand hNoRecognized
  exact candidate_not_relation hCand hNoRecognized

theorem p2_no_channel_rewrite
    {R : GeneratedNormalizerRecognizer} {S : EventFlow}
    {i : Nat} {w v : RawEvent} :
    InducedNormalizes R S i w v -> AdjPair S i w v := by
  intro hRelation
  exact recognized_normalizer_relation_source_level hRelation

def P2FiniteKernelConservative : Prop :=
  forall {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} {m : DisplayAlphabet},
    NormCand candidate S i w v ->
      (List.Mem m w \/ List.Mem m v) ->
      m = BMark.b0 \/ m = BMark.b1

theorem p2_conservative_over_finite_kernel :
    P2FiniteKernelConservative := by
  intro candidate S i w v m _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

def P2BelowHigherRecognition : Prop :=
  forall {R : GeneratedNormalizerRecognizer} {S : EventFlow}
    {i : Nat} {w v : RawEvent},
    InducedNormalizes R S i w v ->
      Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
      Not (FormalCompilerInput CompilerDatum.hostDerivCert) /\
      Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
      Not (FormalCompilerInput CompilerDatum.hostClosureCert)

theorem p2_below_higher_recognition :
    P2BelowHigherRecognition := by
  intro R S i w v _
  constructor
  · intro h
    cases h
  · constructor
    · intro h
      cases h
    · constructor
      · intro h
        cases h
      · constructor
        · intro h
          cases h
        · intro h
          cases h

structure P2AuditChecklist where
  allAdjacentPairsListable :
    forall {S : EventFlow} {i : Nat} {w v : RawEvent},
      AdjPair S i w v -> LiteralAdjacentPairListing S i w v
  literalCandidateSeparated :
    forall {candidate : RawEvent -> RawEvent -> Prop}
      {S : EventFlow} {i : Nat} {w v : RawEvent},
      NormCand candidate S i w v ->
        (forall R : GeneratedNormalizerRecognizer,
          Not (RecognizesNormalizer R S i w v)) ->
        Not (exists R : GeneratedNormalizerRecognizer,
          InducedNormalizes R S i w v)
  candidateMarkingHasPolicy :
    forall {R : GeneratedCandidatePolicyRecognizer}
      {P : CandidatePolicyFlow} {S : EventFlow}
      {i : Nat} {w v : RawEvent},
      CandidateMarkedByPolicy R P S i w v ->
        RecognizesCandidatePolicy R P
  recognizedRelationsSound :
    forall {R : GeneratedNormalizerRecognizer} {S : EventFlow}
      {i : Nat} {w v : RawEvent},
      NormalizerSoundness R ->
        RecognizesNormalizer R S i w v ->
        InducedNormalizes R S i w v
  preNormalPreserved :
    forall {candidate : RawEvent -> RawEvent -> Prop}
      {S : EventFlow} {i : Nat} {w v : RawEvent},
      NormCand candidate S i w v -> List.Mem w S
  channelRewriteRejected :
    forall {R : GeneratedNormalizerRecognizer} {S : EventFlow}
      {i : Nat} {w v : RawEvent},
      InducedNormalizes R S i w v -> AdjPair S i w v
  hiddenPackageRejected :
    Not (FormalCompilerInput CompilerDatum.hostPkg)
  hiddenNameCertRejected :
    Not (FormalCompilerInput CompilerDatum.hostNameCert)
  acceptedExportHasCertificates :
    forall {S : EventFlow},
      AcceptedObjectFlow S ->
        exists N C : EventFlow,
          RecognizedNameCertFlow N /\ RecognizedClosureCertFlow C

def P2Adequate (P : List DisplayAlphabet -> Option EventFlow) : Prop :=
  P1Adequate P /\
    P2AuditChecklist /\
    (forall {R : GeneratedNormalizerRecognizer} {S : EventFlow}
      {i : Nat} {w v : RawEvent},
      RecognizesNormalizer R S i w v -> InducedNormalizes R S i w v) /\
    P2BelowHigherRecognition

theorem p2_adequacy
    {P : List DisplayAlphabet -> Option EventFlow} :
    P1Adequate P ->
      P2AuditChecklist ->
      (forall {R : GeneratedNormalizerRecognizer} {S : EventFlow}
        {i : Nat} {w v : RawEvent},
        RecognizesNormalizer R S i w v -> NormalizerSoundness R) ->
      P2Adequate P := by
  intro hP1 hChecklist hBacked
  constructor
  · exact hP1
  · constructor
    · exact hChecklist
    · constructor
      · intro R S i w v hRecognized
        exact (hBacked hRecognized) hRecognized
      · exact p2_below_higher_recognition

theorem p2_adequacy_not_higher
    {P : List DisplayAlphabet -> Option EventFlow} :
    P2Adequate P -> Not (HigherLayerAdequacy P) := by
  intro _ hHigher
  cases hHigher

end BEDC.GroundCompiler.SourceNormalizer
