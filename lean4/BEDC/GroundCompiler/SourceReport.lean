import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.SourceReport

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def EventSegment (w : RawEvent) : List DisplayAlphabet :=
  EventEncoding w

def BodyTerminatorSegments (w : RawEvent) :
    List DisplayAlphabet × List DisplayAlphabet :=
  (BodyEncoding w, EventTerminator)

def BodySegment (w : RawEvent) : List DisplayAlphabet :=
  (BodyTerminatorSegments w).fst

def TerminatorSegment (_w : RawEvent) : List DisplayAlphabet :=
  EventTerminator

theorem event_segment_body_terminator (w : RawEvent) :
    EventSegment w = BodySegment w ++ TerminatorSegment w := by
  rfl

theorem event_segments_partition (S : EventFlow) :
    FlowEncoding S = (List.map EventSegment S).flatten := by
  induction S with
  | nil =>
      rfl
  | cons w rest ih =>
      simp [FlowEncoding, EventSegment, ih]

end BEDC.GroundCompiler.SourceReport
