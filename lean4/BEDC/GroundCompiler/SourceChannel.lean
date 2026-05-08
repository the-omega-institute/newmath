import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.SourceChannel

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

def SourceLayer : Type :=
  RawEvent ⊕ EventFlow

def ChannelLayer : Type :=
  { c : List DisplayAlphabet // LegalZStream c }

def SourceLevelRelation : Type :=
  RawEvent -> RawEvent -> Prop

def SourceCarryLedger (w v : RawEvent) : EventFlow :=
  [w, v]

def LedgerPreserving
    (rel : SourceLevelRelation) (record : RawEvent -> RawEvent -> EventFlow) :
    Prop :=
  forall w v : RawEvent, rel w v -> record w v = SourceCarryLedger w v

def NormalizeChannel
    (N : EventFlow -> EventFlow) (c : List DisplayAlphabet) :
    Option (List DisplayAlphabet) :=
  match Decode c with
  | some S => some (FlowEncoding (N S))
  | none => none

def ContiguousSubstring
    (u c : List DisplayAlphabet) : Prop :=
  exists pre post : List DisplayAlphabet, c = pre ++ u ++ post

def OccursAsDecodedEvent
    (u c : List DisplayAlphabet) : Prop :=
  exists S : EventFlow, Decode c = some S /\ List.Mem u S

structure SourceLevelClassifier where
  Object : Type
  classify : RawEvent -> Object

def SourceLevelClassifiedObject (C : SourceLevelClassifier) : Type :=
  C.Object

def CarryPreNormal : RawEvent :=
  [BMark.b0, BMark.b1, BMark.b1]

def CarryNormal : RawEvent :=
  [BMark.b1, BMark.b0, BMark.b0]

inductive CarryClassifiedObject : Type where
  | carryClass

def CarryClassifier : SourceLevelClassifier :=
  { Object := CarryClassifiedObject,
    classify := fun _ => CarryClassifiedObject.carryClass }

theorem ledger_records_distinguish_ordered_pairs
    {w v w' v' : RawEvent} :
    SourceCarryLedger w v = SourceCarryLedger w' v' -> w = w' /\ v = v' := by
  intro h
  cases h
  constructor
  · rfl
  · rfl

theorem normal_address_does_not_erase_raw_event
    (w v : RawEvent) :
    Not (SourceCarryLedger w v = [v]) := by
  intro h
  cases h

theorem normalize_channel_preserves_legality
    (N : EventFlow -> EventFlow) {c : List DisplayAlphabet} :
    LegalZStream c ->
      exists out : List DisplayAlphabet,
        NormalizeChannel N c = some out /\ LegalZStream out := by
  intro hLegal
  cases legal_stream_completeness hLegal with
  | intro S hDecoded =>
      cases hDecoded with
      | intro hDecode _ =>
          refine ⟨FlowEncoding (N S), ?_, ?_⟩
          · simp [NormalizeChannel, hDecode]
          · exact flow_encoding_legal_zstream (N S)

theorem normalizer_output_factors_through_decoding
    (N : EventFlow -> EventFlow) {c out : List DisplayAlphabet} :
    NormalizeChannel N c = some out ->
      exists S : EventFlow,
        Decode c = some S /\ out = FlowEncoding (N S) := by
  intro h
  unfold NormalizeChannel at h
  cases hDecode : Decode c with
  | none =>
      rw [hDecode] at h
      cases h
  | some S =>
      rw [hDecode] at h
      refine ⟨S, rfl, ?_⟩
      cases h
      rfl

theorem source_normalization_conservative_over_decoding
    (N : EventFlow -> EventFlow) {c : List DisplayAlphabet} :
    LegalZStream c ->
      exists out : List DisplayAlphabet,
        NormalizeChannel N c = some out /\ LegalZStream out := by
  exact normalize_channel_preserves_legality N

theorem channel_level_source_rewrite_may_destroy_legality :
    LegalZStream (EventEncoding [BMark.b0, BMark.b1, BMark.b1]) /\
      Not (LegalZStream
        [BMark.b0, BMark.b1, BMark.b0, BMark.b1,
          BMark.b1, BMark.b0, BMark.b0]) := by
  constructor
  · exact flow_encoding_legal_zstream [[BMark.b0, BMark.b1, BMark.b1]]
  · intro hLegal
    cases legal_stream_completeness hLegal with
    | intro S hDecoded =>
        cases hDecoded with
        | intro hDecode _ =>
            simp [Decode, DecodeFuel, DecEvent] at hDecode

theorem channel_terminator_not_source_event_11 :
    Not (EventTerminator = EventEncoding [BMark.b1, BMark.b1]) := by
  intro h
  simp [EventTerminator, EventEncoding, BodyEncoding] at h

theorem source_event_11_unambiguous :
    Decode (EventEncoding [BMark.b1, BMark.b1]) =
      some [[BMark.b1, BMark.b1]] := by
  exact flow_level_round_trip [[BMark.b1, BMark.b1]]

theorem channel_substring_not_source_event :
    exists c u : List DisplayAlphabet,
      LegalZStream c /\
        ContiguousSubstring u c /\
        Not (OccursAsDecodedEvent u c) := by
  refine
    ⟨EventEncoding [BMark.b1], [BMark.b0, BMark.b1, BMark.b1], ?_, ?_, ?_⟩
  · exact flow_encoding_legal_zstream [[BMark.b1]]
  · exact ⟨[BMark.b1], [], rfl⟩
  · intro hOccurs
    cases hOccurs with
    | intro S hS =>
        cases hS with
        | intro hDecode hMem =>
            have hRound :
                Decode (EventEncoding [BMark.b1]) = some [[BMark.b1]] :=
              flow_level_round_trip [[BMark.b1]]
            rw [hRound] at hDecode
            cases hDecode
            cases hMem with
            | tail _ hTail =>
                cases hTail

theorem carry_events_distinct :
    Not (CarryPreNormal = CarryNormal) := by
  intro h
  cases h

theorem classified_object_map_not_injective :
    exists C : SourceLevelClassifier,
      exists w v : RawEvent,
        Not (w = v) /\ C.classify w = C.classify v := by
  exact
    ⟨CarryClassifier, CarryPreNormal, CarryNormal,
      carry_events_distinct, rfl⟩

theorem quotient_may_be_many_to_one_ledger_lossless :
    exists C : SourceLevelClassifier,
      exists w v : RawEvent,
        Not (w = v) /\
          C.classify w = C.classify v /\
          SourceCarryLedger w v = [w, v] /\
          Not (SourceCarryLedger w v = [v]) := by
  exact
    ⟨CarryClassifier, CarryPreNormal, CarryNormal,
      carry_events_distinct, rfl, rfl,
      normal_address_does_not_erase_raw_event CarryPreNormal CarryNormal⟩

theorem bijection_only_at_raw_layer :
    (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      exists C : SourceLevelClassifier,
        exists w v : RawEvent,
          Not (w = v) /\ C.classify w = C.classify v := by
  constructor
  · exact flow_level_round_trip
  · exact classified_object_map_not_injective

theorem layer_separation :
    (forall S : EventFlow, LegalZStream (FlowEncoding S)) /\
      (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      Not (EventTerminator = EventEncoding [BMark.b1, BMark.b1]) /\
      exists c u : List DisplayAlphabet,
        LegalZStream c /\
          ContiguousSubstring u c /\
          Not (OccursAsDecodedEvent u c) := by
  constructor
  · exact flow_encoding_legal_zstream
  · constructor
    · exact flow_level_round_trip
    · constructor
      · exact channel_terminator_not_source_event_11
      · exact channel_substring_not_source_event

theorem source_analysis_after_decoding :
    (exists c u : List DisplayAlphabet,
      LegalZStream c /\
        ContiguousSubstring u c /\
        Not (OccursAsDecodedEvent u c)) /\
      (forall u c : List DisplayAlphabet,
        OccursAsDecodedEvent u c ->
          exists S : EventFlow, Decode c = some S /\ List.Mem u S) := by
  constructor
  · exact channel_substring_not_source_event
  · intro u c hOccurs
    exact hOccurs

end BEDC.GroundCompiler.SourceChannel
