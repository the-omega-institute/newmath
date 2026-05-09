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

def SourceEventReport (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  Decode c = some S /\ FlowEncoding S = c

def SourceReportPrototype
    (P : List DisplayAlphabet -> Option EventFlow) : Prop :=
  forall c : List DisplayAlphabet,
    forall S : EventFlow, P c = some S -> SourceEventReport c S

theorem event_segment_body_terminator (w : RawEvent) :
    EventSegment w = BodySegment w ++ TerminatorSegment w := by
  rfl

theorem event_segments_partition (S : EventFlow) :
    FlowEncoding S = (List.map EventSegment S).flatten := by
  induction S with
  | nil =>
      rfl
  | cons w rest ih =>
      change
        EventEncoding w ++ FlowEncoding rest =
          EventSegment w ++ (List.map EventSegment rest).flatten
      rw [ih]
      rfl

theorem source_report_may_display_segments {c : List DisplayAlphabet}
    {S : EventFlow} :
    SourceEventReport c S -> c = (List.map EventSegment S).flatten := by
  intro h
  exact Eq.trans (Eq.symm h.right) (event_segments_partition S)

end BEDC.GroundCompiler.SourceReport
