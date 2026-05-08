import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.ChannelEncoding

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

def BodyEncoding : RawEvent -> List DisplayAlphabet
  | [] => []
  | BMark.b0 :: rest => BMark.b0 :: BodyEncoding rest
  | BMark.b1 :: rest => BMark.b1 :: BMark.b0 :: BodyEncoding rest

def EventTerminator : List DisplayAlphabet :=
  [BMark.b1, BMark.b1]

def EventEncoding (w : RawEvent) : List DisplayAlphabet :=
  BodyEncoding w ++ EventTerminator

def LegalEvent (c : List DisplayAlphabet) : Prop :=
  exists w : RawEvent, c = EventEncoding w

def FlowEncoding : EventFlow -> List DisplayAlphabet
  | [] => []
  | w :: rest => EventEncoding w ++ FlowEncoding rest

def LegalZStream (c : List DisplayAlphabet) : Prop :=
  exists S : EventFlow, c = FlowEncoding S

inductive NoAdjacentOneOne : List DisplayAlphabet -> Prop where
  | nil : NoAdjacentOneOne []
  | single (m : DisplayAlphabet) : NoAdjacentOneOne [m]
  | consZero {rest : List DisplayAlphabet} :
      NoAdjacentOneOne rest -> NoAdjacentOneOne (BMark.b0 :: rest)
  | consOneZero {rest : List DisplayAlphabet} :
      NoAdjacentOneOne (BMark.b0 :: rest) ->
        NoAdjacentOneOne (BMark.b1 :: BMark.b0 :: rest)

theorem body_encoding_no_adjacent_11 (w : RawEvent) :
    NoAdjacentOneOne (BodyEncoding w) := by
  induction w with
  | nil =>
      exact NoAdjacentOneOne.nil
  | cons m rest ih =>
      cases m with
      | b0 =>
          exact NoAdjacentOneOne.consZero ih
      | b1 =>
          exact NoAdjacentOneOne.consOneZero
            (NoAdjacentOneOne.consZero ih)

theorem first_11_is_terminator (w : RawEvent) :
    NoAdjacentOneOne (BodyEncoding w) /\
      EventEncoding w = BodyEncoding w ++ EventTerminator := by
  constructor
  · exact body_encoding_no_adjacent_11 w
  · rfl

theorem flow_encoding_legal_zstream (S : EventFlow) :
    LegalZStream (FlowEncoding S) := by
  exact ⟨S, rfl⟩

theorem flow_encoding_not_single_one (S : EventFlow) :
    Not (FlowEncoding S = [BMark.b1]) := by
  intro h
  cases S with
  | nil =>
      cases h
  | cons w rest =>
      cases w with
      | nil =>
          simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at h
      | cons m tail =>
          cases m <;>
            simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at h

theorem channel_encoding_0111_illegal :
    Not (LegalZStream [BMark.b0, BMark.b1, BMark.b1, BMark.b1]) := by
  intro h
  cases h with
  | intro S hS =>
      cases S with
      | nil =>
          cases hS
      | cons w rest =>
          cases w with
          | nil =>
              simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at hS
          | cons m tail =>
              cases m with
              | b0 =>
                  cases tail with
                  | nil =>
                      have hrest : [BMark.b1] = FlowEncoding rest := by
                        simpa [FlowEncoding, EventEncoding, BodyEncoding,
                          EventTerminator] using hS
                      exact flow_encoding_not_single_one rest hrest.symm
                  | cons n tailRest =>
                      cases n <;>
                        simp [FlowEncoding, EventEncoding, BodyEncoding,
                          EventTerminator] at hS
              | b1 =>
                  simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at hS

end BEDC.GroundCompiler.ChannelEncoding
