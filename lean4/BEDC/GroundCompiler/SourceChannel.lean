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

def NormalizeChannel
    (N : EventFlow -> EventFlow) (c : List DisplayAlphabet) :
    Option (List DisplayAlphabet) :=
  match Decode c with
  | some S => some (FlowEncoding (N S))
  | none => none

theorem ledger_records_distinguish_ordered_pairs
    {w v w' v' : RawEvent} :
    SourceCarryLedger w v = SourceCarryLedger w' v' -> w = w' /\ v = v' := by
  intro h
  cases h
  constructor
  · rfl
  · rfl

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

end BEDC.GroundCompiler.SourceChannel
