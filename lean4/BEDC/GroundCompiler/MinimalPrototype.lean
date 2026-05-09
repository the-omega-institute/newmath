import BEDC.GroundCompiler.ImplementationInterface

namespace BEDC.GroundCompiler.MinimalPrototype

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ImplementationInterface
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

inductive PrototypeLevel : Type where
  | p0
  | p1
  | p2
  | p3
  | p4
  | p5
  | p6
  | p7

def PrototypeLevelRank : PrototypeLevel -> Nat
  | PrototypeLevel.p0 => 0
  | PrototypeLevel.p1 => 1
  | PrototypeLevel.p2 => 2
  | PrototypeLevel.p3 => 3
  | PrototypeLevel.p4 => 4
  | PrototypeLevel.p5 => 5
  | PrototypeLevel.p6 => 6
  | PrototypeLevel.p7 => 7

def PrototypeLevelLE (a b : PrototypeLevel) : Prop :=
  PrototypeLevelRank a <= PrototypeLevelRank b

inductive PrototypeInputRepresentation : Type where
  | eventFlowDisplay (S : EventFlow)
  | channelStreamDisplay (c : List DisplayAlphabet)

def PrototypeEncoder (S : EventFlow) (c : List DisplayAlphabet) : Prop :=
  Compiles S c

inductive RejectReason : Type where
  | danglingOne
  | unfinishedEvent
  | nonBinaryCharacter
  | emptyInputPolicyViolation
  | resourceBoundExcess
  | noncanonicalDisplay

structure RejectReport where
  stream : List DisplayAlphabet
  reason : RejectReason

def RequiredUnitTestVectors : List (RawEvent × List DisplayAlphabet) :=
  [ ([], [BMark.b1, BMark.b1]),
    ([BMark.b0], [BMark.b0, BMark.b1, BMark.b1]),
    ([BMark.b1], [BMark.b1, BMark.b0, BMark.b1, BMark.b1]),
    ([BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b1, BMark.b1]),
    ([BMark.b0, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b0, BMark.b1, BMark.b1]),
    ([BMark.b1, BMark.b0],
      [BMark.b1, BMark.b0, BMark.b0, BMark.b1, BMark.b1]),
    ([BMark.b1, BMark.b1],
      [BMark.b1, BMark.b0, BMark.b1, BMark.b0, BMark.b1, BMark.b1]),
    ([BMark.b0, BMark.b1, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b0, BMark.b1, BMark.b0,
        BMark.b1, BMark.b1]),
    ([BMark.b1, BMark.b0, BMark.b0],
      [BMark.b1, BMark.b0, BMark.b0, BMark.b0, BMark.b1,
        BMark.b1]),
    ([BMark.b0, BMark.b0, BMark.b1, BMark.b1],
      [BMark.b0, BMark.b0, BMark.b1, BMark.b0, BMark.b1,
        BMark.b0, BMark.b1, BMark.b1]) ]

def RequiredRejectTestVectors : List (List DisplayAlphabet × RejectReason) :=
  [ ([BMark.b1], RejectReason.danglingOne),
    ([BMark.b0, BMark.b1, BMark.b1, BMark.b1],
      RejectReason.danglingOne),
    ([BMark.b0, BMark.b1, BMark.b0], RejectReason.unfinishedEvent),
    ([BMark.b1, BMark.b0, BMark.b1], RejectReason.danglingOne),
    ([BMark.b0, BMark.b0, BMark.b0], RejectReason.unfinishedEvent) ]

structure RoundTripTestSuite where
  eventVectors : List RawEvent
  flowVectors : List EventFlow

def RequiredRoundTripTestVectors : RoundTripTestSuite where
  eventVectors :=
    [ [],
      [BMark.b0],
      [BMark.b1],
      [BMark.b0, BMark.b0],
      [BMark.b0, BMark.b1],
      [BMark.b1, BMark.b0],
      [BMark.b1, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b1],
      [BMark.b1, BMark.b0, BMark.b0],
      [BMark.b0, BMark.b0, BMark.b1],
      [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b0, BMark.b0] ]
  flowVectors :=
    [ [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0], [BMark.b0, BMark.b1],
        [BMark.b0, BMark.b1, BMark.b1],
        [BMark.b1, BMark.b0, BMark.b0]],
      [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b1],
        [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
        [BMark.b0, BMark.b1, BMark.b0, BMark.b0]],
      [[BMark.b0, BMark.b1, BMark.b1],
        [BMark.b1, BMark.b0, BMark.b0]],
      [[BMark.b1], [BMark.b1, BMark.b1],
        [BMark.b0, BMark.b1, BMark.b1],
        [BMark.b1, BMark.b0, BMark.b0]] ]

structure DecoderState where
  currentEvent : RawEvent
  completedEvents : EventFlow
  position : Nat
  rejectionReason : Option RejectReason

def PrototypeStreamDecoder (c : List DisplayAlphabet) : Option EventFlow :=
  Decode c

inductive PrototypeDecoderOutput : Type where
  | decoded (S : EventFlow)
  | rejected (report : RejectReport)

inductive DecodeStatus : Type where
  | legal
  | illegal

inductive ReportWarning : Type where
  | carryLookingPair
  | rawEventNotChannelTerminator
  | outputViewOnly
  | higherRecognizerRequired

inductive EventFlowDisplayToken : Type where
  | mark (m : DisplayAlphabet)
  | boundary
  | epsilon
  | whitespace

def EventFlowDisplayFormat : Type :=
  List EventFlowDisplayToken

def ChannelStreamDisplayFormat : Type :=
  List DisplayAlphabet

structure DecodeReport where
  inputStream : List DisplayAlphabet
  status : DecodeStatus
  decodedFlow : Option EventFlow
  eventSegments : EventFlow
  rejectionReason : Option RejectReason
  warnings : List ReportWarning

structure EncodeReport where
  inputFlow : EventFlow
  eventCodes : List (List DisplayAlphabet)
  outputStream : List DisplayAlphabet
  roundTripSucceeded : Bool
  warnings : List ReportWarning

inductive PrototypeReportDatum : Type where
  | reject (report : RejectReport)
  | decode (report : DecodeReport)
  | encode (report : EncodeReport)

inductive PrototypeFormalInputDatum : Type where
  | eventFlowDisplay (S : EventFlow)
  | channelStreamDisplay (c : List DisplayAlphabet)

inductive PrototypeIOView : Type where
  | input (datum : PrototypeFormalInputDatum)
  | report (datum : PrototypeReportDatum)

inductive FormalPrototypeInput : PrototypeIOView -> Prop where
  | eventFlowDisplay (S : EventFlow) :
      FormalPrototypeInput
        (PrototypeIOView.input
          (PrototypeFormalInputDatum.eventFlowDisplay S))
  | channelStreamDisplay (c : List DisplayAlphabet) :
      FormalPrototypeInput
        (PrototypeIOView.input
          (PrototypeFormalInputDatum.channelStreamDisplay c))

inductive PrototypeReportOutputView : PrototypeIOView -> Prop where
  | reject (report : RejectReport) :
      PrototypeReportOutputView
        (PrototypeIOView.report (PrototypeReportDatum.reject report))
  | decode (report : DecodeReport) :
      PrototypeReportOutputView
        (PrototypeIOView.report (PrototypeReportDatum.decode report))
  | encode (report : EncodeReport) :
      PrototypeReportOutputView
        (PrototypeIOView.report (PrototypeReportDatum.encode report))

def PrototypeDecoder
    (c : List DisplayAlphabet) : PrototypeDecoderOutput -> Prop
  | PrototypeDecoderOutput.decoded S => Decodes c S
  | PrototypeDecoderOutput.rejected report => report.stream = c

inductive SyntacticRejectReason : RejectReason -> Prop where
  | danglingOne : SyntacticRejectReason RejectReason.danglingOne
  | unfinishedEvent : SyntacticRejectReason RejectReason.unfinishedEvent
  | nonBinaryCharacter :
      SyntacticRejectReason RejectReason.nonBinaryCharacter

def PrototypeSyntacticReject
    (c : List DisplayAlphabet) (reason : RejectReason) : Prop :=
  PrototypeStreamDecoder c = none /\ SyntacticRejectReason reason

inductive ReferencePrototypePublic : InterfaceDatum -> Prop where
  | compiles :
      ReferencePrototypePublic InterfaceDatum.compiles
  | decodes :
      ReferencePrototypePublic InterfaceDatum.decodes
  | rejects :
      ReferencePrototypePublic InterfaceDatum.rejects
  | isLegalZStream :
      ReferencePrototypePublic InterfaceDatum.isLegalZStream

def ReferencePrototype (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> ReferencePrototypePublic d) /\
    publicSurface InterfaceDatum.compiles /\
    publicSurface InterfaceDatum.decodes /\
    publicSurface InterfaceDatum.rejects /\
    publicSurface InterfaceDatum.isLegalZStream /\
    NoHostLeakCondition publicSurface

inductive HigherPrototypeClaim : InterfaceDatum -> Prop where
  | recognizes :
      HigherPrototypeClaim InterfaceDatum.recognizes
  | certifiedRecognizer :
      HigherPrototypeClaim InterfaceDatum.certifiedRecognizer
  | recognizesPkg :
      HigherPrototypeClaim InterfaceDatum.recognizesPkg
  | recognizesNameCert :
      HigherPrototypeClaim InterfaceDatum.recognizesNameCert
  | recognizesDerivCert :
      HigherPrototypeClaim InterfaceDatum.recognizesDerivCert
  | recognizesTheorem :
      HigherPrototypeClaim InterfaceDatum.recognizesTheorem
  | recognizesChapter :
      HigherPrototypeClaim InterfaceDatum.recognizesChapter
  | recognizesCompiler :
      HigherPrototypeClaim InterfaceDatum.recognizesCompiler
  | acceptFlow :
      HigherPrototypeClaim InterfaceDatum.acceptFlow
  | motifReport :
      HigherPrototypeClaim InterfaceDatum.motifReport
  | metricReport :
      HigherPrototypeClaim InterfaceDatum.metricReport
  | bridgeObligation :
      HigherPrototypeClaim InterfaceDatum.bridgeObligation

inductive AllowedCLICommand : Type where
  | encode
  | decode
  | check
  | roundtrip
  | report

inductive ForbiddenP0CLIMeaning : Type where
  | nameCertificateRecognition
  | theoremRecognition
  | objectAcceptance
  | proof
  | bridge
  | dimensionInference
  | realObjectInference
  | circleObjectInference
  | channelLevelCarryNormalization

structure PrototypeAuditChecklist
    (publicSurface : InterfaceDatum -> Prop) where
  eventEncodingImplements :
    forall w : RawEvent, PrototypeEventEncoder w = EventEncoding w
  flowEncodingImplements :
    forall S : EventFlow, PrototypeFlowEncoder S = FlowEncoding S
  streamDecoderImplements :
    forall c : List DisplayAlphabet, PrototypeStreamDecoder c = Decode c
  danglingOneRejected :
    PrototypeStreamDecoder [BMark.b1] = none
  unfinishedEventRejected :
    PrototypeStreamDecoder [BMark.b0, BMark.b1, BMark.b0] = none
  unitTestsPass :
    forall w c,
      List.Mem (w, c) RequiredUnitTestVectors -> EventEncoding w = c
  roundTripEventTestsPass :
    forall w,
      List.Mem w RequiredRoundTripTestVectors.eventVectors ->
        DecEvent (EventEncoding w) = some (w, [])
  carryWarningsAvailable :
    exists report : DecodeReport,
      List.Mem ReportWarning.carryLookingPair report.warnings
  noHigherRecognitionClaim :
    Not (publicSurface InterfaceDatum.recognizesPkg) /\
      Not (publicSurface InterfaceDatum.recognizesNameCert) /\
      Not (publicSurface InterfaceDatum.recognizesTheorem) /\
      Not (publicSurface InterfaceDatum.acceptFlow)

def ReportIncludesCarryWarning (report : DecodeReport) : Prop :=
  List.Mem ReportWarning.carryLookingPair report.warnings

def P0ChannelObligations : Prop :=
  (forall S : EventFlow, forall c : List DisplayAlphabet,
    PrototypeEncoder S c -> Compiles S c) /\
  (forall c : List DisplayAlphabet, forall S : EventFlow,
    PrototypeDecoder c (PrototypeDecoderOutput.decoded S) -> Decodes c S) /\
  (forall c : List DisplayAlphabet,
    LegalZStream c ->
      exists S : EventFlow, PrototypeStreamDecoder c = some S /\ Decodes c S) /\
  (forall c : List DisplayAlphabet, forall reason : RejectReason,
    PrototypeSyntacticReject c reason -> Not (LegalZStream c))

def P0Adequate (publicSurface : InterfaceDatum -> Prop) : Prop :=
  ReferencePrototype publicSurface /\
    exists _checklist : PrototypeAuditChecklist publicSurface,
      P0ChannelObligations

def HigherPrototypeAdequacy (publicSurface : InterfaceDatum -> Prop) : Prop :=
  exists d : InterfaceDatum, publicSurface d /\ HigherPrototypeClaim d

theorem reference_prototype_not_full_compiler
    {publicSurface : InterfaceDatum -> Prop} {d : InterfaceDatum} :
    ReferencePrototype publicSurface ->
      publicSurface d ->
      Not (HigherPrototypeClaim d) := by
  intro hPrototype hPublic hHigher
  have hCore : ReferencePrototypePublic d := hPrototype.left d hPublic
  cases hCore <;> cases hHigher

theorem prototype_encoder_soundness {S : EventFlow}
    {c : List DisplayAlphabet} :
    PrototypeEncoder S c -> Compiles S c := by
  intro h
  exact h

theorem prototype_decoder_soundness {c : List DisplayAlphabet}
    {S : EventFlow} :
    PrototypeDecoder c (PrototypeDecoderOutput.decoded S) -> Decodes c S := by
  intro h
  exact h

theorem prototype_decoder_completeness_on_legal_streams
    {c : List DisplayAlphabet} :
    LegalZStream c ->
      exists S : EventFlow, PrototypeStreamDecoder c = some S /\ Decodes c S := by
  intro hLegal
  cases legal_stream_completeness hLegal with
  | intro S hS =>
      cases hS with
      | intro hDecode hFlow =>
          exact ⟨S, hDecode, hFlow.symm⟩

theorem prototype_reject_soundness {c : List DisplayAlphabet}
    {reason : RejectReason} :
    PrototypeSyntacticReject c reason -> Not (LegalZStream c) := by
  intro hReject hLegal
  cases hReject with
  | intro hNone _ =>
      cases prototype_decoder_completeness_on_legal_streams hLegal with
      | intro S hS =>
          cases hS with
          | intro hSome _ =>
              rw [hSome] at hNone
              cases hNone

theorem p0_channel_obligations_hold :
    P0ChannelObligations := by
  constructor
  · intro S c h
    exact prototype_encoder_soundness h
  constructor
  · intro c S h
    exact prototype_decoder_soundness h
  constructor
  · intro c hLegal
    exact prototype_decoder_completeness_on_legal_streams hLegal
  · intro c reason hReject
    exact prototype_reject_soundness hReject

theorem reports_must_include_warnings
    {publicSurface : InterfaceDatum -> Prop} :
    PrototypeAuditChecklist publicSurface ->
      exists report : DecodeReport, ReportIncludesCarryWarning report := by
  intro hChecklist
  exact hChecklist.carryWarningsAvailable

theorem prototype_audit_suffices
    {publicSurface : InterfaceDatum -> Prop} :
    PrototypeAuditChecklist publicSurface ->
      ReferencePrototype publicSurface ->
        P0Adequate publicSurface := by
  intro hChecklist hPrototype
  exact ⟨hPrototype, ⟨hChecklist, p0_channel_obligations_hold⟩⟩

theorem p0_adequacy_not_higher
    {publicSurface : InterfaceDatum -> Prop} :
    P0Adequate publicSurface ->
      Not (HigherPrototypeAdequacy publicSurface) := by
  intro hAdequate hHigher
  cases hHigher with
  | intro d hDatum =>
      cases hDatum with
      | intro hPublic hHigherClaim =>
          exact
            reference_prototype_not_full_compiler
              hAdequate.left hPublic hHigherClaim

theorem reference_prototype_not_higher_adequacy
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      Not (HigherPrototypeAdequacy publicSurface) := by
  intro hPrototype hHigher
  cases hHigher with
  | intro d hDatum =>
      cases hDatum with
      | intro hPublic hHigherClaim =>
          exact
            reference_prototype_not_full_compiler
              hPrototype hPublic hHigherClaim

theorem reference_prototype_conservative_over_kernel
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      (forall d, publicSurface d -> ReferencePrototypePublic d) /\
      Not (HigherPrototypeAdequacy publicSurface) /\
      NoHostLeakCondition publicSurface := by
  intro hPrototype
  constructor
  · exact hPrototype.left
  · constructor
    · exact reference_prototype_not_higher_adequacy hPrototype
    · exact hPrototype.right.right.right.right.right

theorem reference_prototype_address_layer
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      publicSurface InterfaceDatum.compiles /\
      publicSurface InterfaceDatum.decodes /\
      publicSurface InterfaceDatum.rejects /\
      publicSurface InterfaceDatum.isLegalZStream /\
      Not (HigherPrototypeAdequacy publicSurface) := by
  intro hPrototype
  constructor
  · exact hPrototype.right.left
  · constructor
    · exact hPrototype.right.right.left
    · constructor
      · exact hPrototype.right.right.right.left
      · constructor
        · exact hPrototype.right.right.right.right.left
        · exact reference_prototype_not_higher_adequacy hPrototype

theorem prototype_reports_output_not_formal_input {v : PrototypeIOView} :
    PrototypeReportOutputView v -> Not (FormalPrototypeInput v) := by
  intro hReport hInput
  cases hReport <;> cases hInput

theorem reject_reports_output_not_formal_input (report : RejectReport) :
    PrototypeReportOutputView
        (PrototypeIOView.report (PrototypeReportDatum.reject report)) /\
      Not (FormalPrototypeInput
        (PrototypeIOView.report (PrototypeReportDatum.reject report))) := by
  constructor
  · exact PrototypeReportOutputView.reject report
  · intro hInput
    cases hInput

theorem reference_prototype_no_math_structure_recognition
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      Not (publicSurface InterfaceDatum.recognizesPkg) /\
      Not (publicSurface InterfaceDatum.recognizesNameCert) /\
      Not (publicSurface InterfaceDatum.recognizesDerivCert) /\
      Not (publicSurface InterfaceDatum.recognizesTheorem) /\
      Not (publicSurface InterfaceDatum.recognizesChapter) /\
      Not (publicSurface InterfaceDatum.motifReport) /\
      Not (publicSurface InterfaceDatum.metricReport) /\
      Not (publicSurface InterfaceDatum.acceptFlow) := by
  intro hPrototype
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.recognizesPkg
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.recognizesNameCert
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.recognizesDerivCert
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.recognizesTheorem
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.recognizesChapter
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.motifReport
  constructor
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.metricReport
  · intro hPublic
    exact reference_prototype_not_full_compiler hPrototype hPublic
      HigherPrototypeClaim.acceptFlow

theorem prototype_output_not_namecert
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      Not (publicSurface InterfaceDatum.recognizesNameCert) := by
  intro hPrototype hPublic
  exact reference_prototype_not_full_compiler hPrototype hPublic
    HigherPrototypeClaim.recognizesNameCert

theorem prototype_output_not_theorem
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      Not (publicSurface InterfaceDatum.recognizesTheorem) := by
  intro hPrototype hPublic
  exact reference_prototype_not_full_compiler hPrototype hPublic
    HigherPrototypeClaim.recognizesTheorem

theorem prototype_output_not_accepted
    {publicSurface : InterfaceDatum -> Prop} :
    ReferencePrototype publicSurface ->
      Not (publicSurface InterfaceDatum.acceptFlow) := by
  intro hPrototype hPublic
  exact reference_prototype_not_full_compiler hPrototype hPublic
    HigherPrototypeClaim.acceptFlow

end BEDC.GroundCompiler.MinimalPrototype
