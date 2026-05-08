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

end BEDC.GroundCompiler.ChannelEncoding
