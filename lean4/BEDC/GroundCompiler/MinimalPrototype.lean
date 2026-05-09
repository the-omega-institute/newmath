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

structure DecodeReport where
  inputStream : List DisplayAlphabet
  status : DecodeStatus
  decodedFlow : Option EventFlow
  eventSegments : EventFlow
  rejectionReason : Option RejectReason
  warnings : List ReportWarning

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
