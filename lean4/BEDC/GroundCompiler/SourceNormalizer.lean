import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SourceNormalizer

open BEDC.GroundCompiler.EventFlow

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

inductive P2Warning : Type where
  | candidateOnly
  | recognizerMissing
  | noCarryClaim
  | noChannelRewrite

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

end BEDC.GroundCompiler.SourceNormalizer
