import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.SourceReport

open BEDC.FKernel.Mark
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

def IllegalInputReport (c : List DisplayAlphabet) : Prop :=
  Not (LegalZStream c) /\
    forall S : EventFlow, Not (SourceEventReport c S)

def RoundTripReport (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  Decode c = some S /\ FlowEncoding S = c

def Decodes (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  Decode c = some S

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

inductive HighRiskRawEvent : RawEvent -> Prop where
  | event01 :
      HighRiskRawEvent [BMark.b0, BMark.b1]
  | event011 :
      HighRiskRawEvent [BMark.b0, BMark.b1, BMark.b1]
  | event100 :
      HighRiskRawEvent [BMark.b1, BMark.b0, BMark.b0]
  | event001 :
      HighRiskRawEvent [BMark.b0, BMark.b0, BMark.b1]
  | event0011 :
      HighRiskRawEvent [BMark.b0, BMark.b0, BMark.b1, BMark.b1]
  | event0100 :
      HighRiskRawEvent [BMark.b0, BMark.b1, BMark.b0, BMark.b0]

def CannotClaimCoverage (annotations : List CannotClaimAnnotation) : Prop :=
  List.Mem CannotClaimAnnotation.decodedEventFlowNotTheoremhood annotations /\
    List.Mem CannotClaimAnnotation.decodedEventFlowNotNameCert annotations /\
    List.Mem CannotClaimAnnotation.decodedEventFlowNotDerivCert annotations /\
    List.Mem CannotClaimAnnotation.decodedEventFlowNotAcceptanceGate annotations /\
    List.Mem CannotClaimAnnotation.reportNotProof annotations /\
    List.Mem CannotClaimAnnotation.reportNotPackageRecognition annotations

def NontrivialCannotClaimPolicy
    (S : EventFlow) (annotations : List CannotClaimAnnotation) : Prop :=
  (exists w : RawEvent, List.Mem w S /\ HighRiskRawEvent w) ->
    CannotClaimCoverage annotations

inductive HigherLayerAdequacy
    (_P : List DisplayAlphabet -> Option EventFlow) : Prop

inductive MathematicalObjectGenerator
    (_P : List DisplayAlphabet -> Option EventFlow) : Prop

def SoundSourceReport (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  LegalZStream c /\
    SourceEventReport c S /\
    c = (List.map EventSegment S).flatten

structure DisplayPolicy where
  printsRawEventSeparator : Bool
  printsEmptyEventMarker : Bool
  printsEventIndex : Bool
  printsBodySegment : Bool
  printsTerminatorSegment : Bool
  printsEventCode : Bool
  printsWarnings : Bool
  printsCannotClaims : Bool

structure MinimalSourceEventReportFormat where
  containsInputChannelStream : Bool
  containsLegalStatus : Bool
  containsDecodedEventFlowDisplay : Bool
  containsEventIndex : Bool
  containsRawEvent : Bool
  containsBodyCode : Bool
  containsTerminatorCode : Bool
  containsFullEventCode : Bool
  containsRoundTripStatus : Bool
  containsLiteralSourceWarnings : Bool
  containsCannotClaimAnnotations : Bool

def CanonicalDisplayPolicy : DisplayPolicy where
  printsRawEventSeparator := true
  printsEmptyEventMarker := true
  printsEventIndex := true
  printsBodySegment := true
  printsTerminatorSegment := true
  printsEventCode := true
  printsWarnings := true
  printsCannotClaims := true

inductive SourceReportRecognition
    (_c : List DisplayAlphabet) (_S : EventFlow) : Prop

inductive ReportDatum : Type where
  | sourceReport (c : List DisplayAlphabet) (S : EventFlow)
  | hostPythonList
  | hostJSONPackage
  | hostYAMLChapter
  | hostStringTheoremLabel
  | hostEnumStatus

inductive HostLeakInReport : ReportDatum -> Prop where
  | hostPythonList :
      HostLeakInReport ReportDatum.hostPythonList
  | hostJSONPackage :
      HostLeakInReport ReportDatum.hostJSONPackage
  | hostYAMLChapter :
      HostLeakInReport ReportDatum.hostYAMLChapter
  | hostStringTheoremLabel :
      HostLeakInReport ReportDatum.hostStringTheoremLabel
  | hostEnumStatus :
      HostLeakInReport ReportDatum.hostEnumStatus

inductive AdmissibleSourceReportDatum : ReportDatum -> Prop where
  | sourceReport (c : List DisplayAlphabet) (S : EventFlow) :
      SourceEventReport c S ->
        AdmissibleSourceReportDatum (ReportDatum.sourceReport c S)

structure P1AuditChecklist
    (P : List DisplayAlphabet -> Option EventFlow) where
  reportsAreSourceReports :
    forall c : List DisplayAlphabet,
      forall S : EventFlow, P c = some S -> SourceEventReport c S
  illegalInputsRejected :
    forall c : List DisplayAlphabet, Not (LegalZStream c) -> P c = none
  reportsDoNotBecomeInputs :
    forall c : List DisplayAlphabet,
      forall S : EventFlow, P c = some S -> Not (SourceReportFormalInput c S)
  hostLeaksRejected :
    forall d : ReportDatum,
      HostLeakInReport d -> Not (AdmissibleSourceReportDatum d)

def P1Adequate (P : List DisplayAlphabet -> Option EventFlow) : Prop :=
  SourceReportPrototype P /\
    (forall c : List DisplayAlphabet, Not (LegalZStream c) -> P c = none) /\
    (forall c : List DisplayAlphabet,
      forall S : EventFlow, P c = some S -> Not (SourceReportFormalInput c S))

def AddressReportLayer (P : List DisplayAlphabet -> Option EventFlow) : Prop :=
  P1Adequate P /\
    Not (HigherLayerAdequacy P) /\
    Not (MathematicalObjectGenerator P)

def PolicyDecode (_policy : DisplayPolicy)
    (c : List DisplayAlphabet) : Option EventFlow :=
  Decode c

def PolicyCompile (_policy : DisplayPolicy) (S : EventFlow) :
    List DisplayAlphabet :=
  FlowEncoding S

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

theorem warnings_weaker_than_recognitions
    (warning : LiteralSourceWarning) :
    Not (LiteralWarningRecognition warning) :=
  literal_warning_not_recognition warning

theorem cannot_claims_prevent_overinterpretation
    {w : RawEvent} {annotations : List CannotClaimAnnotation} :
    HighRiskRawEvent w ->
      CannotClaimCoverage annotations ->
        List.Mem CannotClaimAnnotation.reportNotProof annotations /\
        List.Mem CannotClaimAnnotation.decodedEventFlowNotTheoremhood annotations /\
        List.Mem CannotClaimAnnotation.decodedEventFlowNotNameCert annotations /\
        List.Mem CannotClaimAnnotation.decodedEventFlowNotDerivCert annotations /\
        List.Mem CannotClaimAnnotation.decodedEventFlowNotAcceptanceGate annotations /\
        List.Mem CannotClaimAnnotation.reportNotPackageRecognition annotations := by
  intro _ hCoverage
  exact
    And.intro hCoverage.right.right.right.right.left
      (And.intro hCoverage.left
        (And.intro hCoverage.right.left
          (And.intro hCoverage.right.right.left
            (And.intro hCoverage.right.right.right.left
              hCoverage.right.right.right.right.right))))

theorem source_report_nontrivial_cannot_claims
    {S : EventFlow} {annotations : List CannotClaimAnnotation} :
    NontrivialCannotClaimPolicy S annotations ->
      (exists w : RawEvent, List.Mem w S /\ HighRiskRawEvent w) ->
        CannotClaimCoverage annotations := by
  intro hPolicy hRisk
  exact hPolicy hRisk

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

theorem illegal_input_report_from_illegal {c : List DisplayAlphabet} :
    Not (LegalZStream c) -> IllegalInputReport c := by
  intro hIllegal
  exact ⟨hIllegal, fun S => illegal_channel_no_source_report hIllegal⟩

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

theorem source_report_sound_report {c : List DisplayAlphabet}
    {S : EventFlow} :
    SoundSourceReport c S -> Decodes c S := by
  intro h
  exact h.right.left.left

theorem source_report_preserves_raw_flow {c : List DisplayAlphabet}
    {S : EventFlow} :
    SoundSourceReport c S ->
      SourceEventReport c S /\ c = (List.map EventSegment S).flatten := by
  intro h
  exact h.right

theorem source_report_does_not_recognize_structures
    {c : List DisplayAlphabet} {S : EventFlow} :
    SoundSourceReport c S -> Not (SourceReportRecognition c S) := by
  intro _ hRecognition
  cases hRecognition

theorem display_policy_not_semantics (policy : DisplayPolicy)
    {c : List DisplayAlphabet} {S : EventFlow} :
    SourceEventReport c S ->
      PolicyDecode policy c = some S /\ PolicyCompile policy S = c := by
  intro h
  exact And.intro h.left h.right

theorem display_policy_roundtrip (leftPolicy rightPolicy : DisplayPolicy)
    {c : List DisplayAlphabet} {S : EventFlow} :
    SourceEventReport c S ->
      PolicyDecode leftPolicy c = some S /\
      PolicyDecode rightPolicy c = some S /\
      PolicyCompile leftPolicy S = c /\
      PolicyCompile rightPolicy S = c := by
  intro h
  exact And.intro h.left (And.intro h.left (And.intro h.right h.right))

theorem host_leak_inadmissible {d : ReportDatum} :
    HostLeakInReport d -> Not (AdmissibleSourceReportDatum d) := by
  intro hLeak hAdmissible
  cases hLeak <;> cases hAdmissible

theorem json_yaml_reports_view_only :
    Not (AdmissibleSourceReportDatum ReportDatum.hostJSONPackage) /\
      Not (AdmissibleSourceReportDatum ReportDatum.hostYAMLChapter) := by
  exact
    And.intro
      (host_leak_inadmissible HostLeakInReport.hostJSONPackage)
      (host_leak_inadmissible HostLeakInReport.hostYAMLChapter)

theorem p1_adequacy {P : List DisplayAlphabet -> Option EventFlow} :
    P1AuditChecklist P -> P1Adequate P := by
  intro h
  exact
    And.intro h.reportsAreSourceReports
      (And.intro h.illegalInputsRejected h.reportsDoNotBecomeInputs)

theorem p1_adequacy_not_higher
    {P : List DisplayAlphabet -> Option EventFlow} :
    P1Adequate P -> Not (HigherLayerAdequacy P) := by
  intro _ hHigher
  cases hHigher

theorem source_report_conservative {c : List DisplayAlphabet}
    {S : EventFlow} :
    SourceEventReport c S ->
      (forall w : RawEvent,
        List.Mem w S ->
          forall m : DisplayAlphabet, List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) /\
      Not (SourceReportRecognition c S) := by
  intro _
  exact
    And.intro
      (fun w hw m hm =>
        BEDC.GroundCompiler.EventFlow.event_flow_conservativity hw hm)
      (fun hRecognition => by
        cases hRecognition)

theorem p1_address_report_layer
    {P : List DisplayAlphabet -> Option EventFlow} :
    P1Adequate P -> AddressReportLayer P := by
  intro hAdequate
  exact
    And.intro hAdequate
      (And.intro (p1_adequacy_not_higher hAdequate)
        (fun hGenerator => by
          cases hGenerator))

end BEDC.GroundCompiler.SourceReport
