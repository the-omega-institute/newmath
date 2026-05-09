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

def RoundTripReport (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  Decode c = some S /\ FlowEncoding S = c

inductive SourceReportFormalInput
    (_c : List DisplayAlphabet) (_S : EventFlow) : Prop

inductive EventIndex : EventFlow -> Nat -> RawEvent -> Prop where
  | here (w : RawEvent) (rest : EventFlow) :
      EventIndex (w :: rest) 0 w
  | there (head w : RawEvent) (rest : EventFlow) (i : Nat) :
      EventIndex rest i w -> EventIndex (head :: rest) (i + 1) w

inductive LiteralSourceWarning : Type where
  | adjacentCarryCandidate
  | adjacentSourceOnes
  | completionWitnessCandidate
  | normalAddressCandidate

inductive LiteralWarningRecognition : LiteralSourceWarning -> Prop

inductive CannotClaimAnnotation : Type where
  | decodedEventFlowNotTheoremhood
  | decodedEventFlowNotNameCert
  | decodedEventFlowNotDerivCert
  | decodedEventFlowNotAcceptanceGate
  | literalCarryRequiresRecognizer
  | terminatorNotSourceEvent
  | reportNotProof
  | reportNotPackageRecognition

def SoundSourceReport (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  LegalZStream c /\
    SourceEventReport c S /\
    c = (List.map EventSegment S).flatten

theorem event_segment_body_terminator (w : RawEvent) :
    EventSegment w = BodySegment w ++ TerminatorSegment w := by
  rfl

theorem source_report_output_not_input {c : List DisplayAlphabet}
    {S : EventFlow} :
    SourceEventReport c S -> Not (SourceReportFormalInput c S) := by
  intro _ hInput
  cases hInput

theorem literal_warning_not_recognition (warning : LiteralSourceWarning) :
    Not (LiteralWarningRecognition warning) := by
  intro h
  cases h

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

theorem illegal_channel_no_source_report {c : List DisplayAlphabet}
    {S : EventFlow} :
    Not (LegalZStream c) -> Not (SourceEventReport c S) := by
  intro hIllegal hReport
  exact hIllegal ⟨S, hReport.right.symm⟩

theorem roundtrip_report_determined :
    (forall S : EventFlow, RoundTripReport (FlowEncoding S) S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c -> exists S : EventFlow, RoundTripReport c S) := by
  constructor
  · intro S
    exact And.intro (flow_level_round_trip S) rfl
  · intro c hLegal
    cases legal_stream_completeness hLegal with
    | intro S hReport =>
        exact ⟨S, hReport⟩

end BEDC.GroundCompiler.SourceReport
