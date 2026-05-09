import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.ProgrammaticRealization

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

inductive ChannelDFAState : Type where
  | boundary
  | body
  | sawOne
  | dead

def ChannelDFAStep : ChannelDFAState -> DisplayAlphabet -> ChannelDFAState
  | ChannelDFAState.boundary, BMark.b0 => ChannelDFAState.body
  | ChannelDFAState.boundary, BMark.b1 => ChannelDFAState.sawOne
  | ChannelDFAState.body, BMark.b0 => ChannelDFAState.body
  | ChannelDFAState.body, BMark.b1 => ChannelDFAState.sawOne
  | ChannelDFAState.sawOne, BMark.b0 => ChannelDFAState.body
  | ChannelDFAState.sawOne, BMark.b1 => ChannelDFAState.boundary
  | ChannelDFAState.dead, _ => ChannelDFAState.dead

def ChannelDFARun : ChannelDFAState -> List DisplayAlphabet -> ChannelDFAState
  | q, [] => q
  | q, m :: rest => ChannelDFARun (ChannelDFAStep q m) rest

def ChannelDFAAccept (c : List DisplayAlphabet) : Prop :=
  ChannelDFARun ChannelDFAState.boundary c = ChannelDFAState.boundary

structure ExecutableChannelCore where
  encodeMark : DisplayAlphabet -> List DisplayAlphabet
  encodeEvent : RawEvent -> List DisplayAlphabet
  encodeFlow : EventFlow -> List DisplayAlphabet
  decode : List DisplayAlphabet -> Option EventFlow
  markZero : encodeMark BMark.b0 = [BMark.b0]
  markOne : encodeMark BMark.b1 = [BMark.b1, BMark.b0]
  event_eq : forall w : RawEvent, encodeEvent w = EventEncoding w
  flow_eq : forall S : EventFlow, encodeFlow S = FlowEncoding S
  decode_eq : forall c : List DisplayAlphabet, decode c = Decode c

def referenceExecutableChannelCore : ExecutableChannelCore where
  encodeMark
    | BMark.b0 => [BMark.b0]
    | BMark.b1 => [BMark.b1, BMark.b0]
  encodeEvent := EventEncoding
  encodeFlow := FlowEncoding
  decode := Decode
  markZero := rfl
  markOne := rfl
  event_eq := by
    intro _
    rfl
  flow_eq := by
    intro _
    rfl
  decode_eq := by
    intro _
    rfl

theorem channel_dfa_run_append
    (q : ChannelDFAState) (xs ys : List DisplayAlphabet) :
    ChannelDFARun q (xs ++ ys) = ChannelDFARun (ChannelDFARun q xs) ys := by
  induction xs generalizing q with
  | nil =>
      rfl
  | cons m rest ih =>
      simp [ChannelDFARun, ih]

theorem event_encoding_dfa_accepts_from_boundary_and_body
    (w : RawEvent) :
    ChannelDFARun ChannelDFAState.boundary (EventEncoding w) =
      ChannelDFAState.boundary /\
    ChannelDFARun ChannelDFAState.body (EventEncoding w) =
      ChannelDFAState.boundary := by
  induction w with
  | nil =>
      simp [EventEncoding, BodyEncoding, EventTerminator, ChannelDFARun,
        ChannelDFAStep]
  | cons m rest ih =>
      cases m with
      | b0 =>
          constructor
          · simpa [EventEncoding, BodyEncoding, ChannelDFARun, ChannelDFAStep]
              using ih.right
          · simpa [EventEncoding, BodyEncoding, ChannelDFARun, ChannelDFAStep]
              using ih.right
      | b1 =>
          constructor
          · simpa [EventEncoding, BodyEncoding, ChannelDFARun, ChannelDFAStep]
              using ih.right
          · simpa [EventEncoding, BodyEncoding, ChannelDFARun, ChannelDFAStep]
              using ih.right

theorem flow_encoding_dfa_accepts (S : EventFlow) :
    ChannelDFAAccept (FlowEncoding S) := by
  induction S with
  | nil =>
      rfl
  | cons w rest ih =>
      change
        ChannelDFARun ChannelDFAState.boundary
          (EventEncoding w ++ FlowEncoding rest) = ChannelDFAState.boundary
      rw [channel_dfa_run_append]
      rw [(event_encoding_dfa_accepts_from_boundary_and_body w).left]
      exact ih

theorem base_language_stream_regular {c : List DisplayAlphabet} :
    LegalZStream c -> ChannelDFAAccept c := by
  intro hLegal
  cases hLegal with
  | intro S hS =>
      rw [hS]
      exact flow_encoding_dfa_accepts S

structure ExecutableP0Realization where
  core : ExecutableChannelCore
  legal : List DisplayAlphabet -> Prop
  legal_eq : forall c : List DisplayAlphabet, legal c <-> LegalZStream c
  roundTrip : forall S : EventFlow, core.decode (core.encodeFlow S) = some S

def referenceExecutableP0Realization : ExecutableP0Realization where
  core := referenceExecutableChannelCore
  legal := LegalZStream
  legal_eq := by
    intro c
    constructor
    · intro h
      exact h
    · intro h
      exact h
  roundTrip := by
    intro S
    exact flow_level_round_trip S

end BEDC.GroundCompiler.ProgrammaticRealization
