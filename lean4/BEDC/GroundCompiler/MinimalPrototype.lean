import BEDC.GroundCompiler.ImplementationInterface

namespace BEDC.GroundCompiler.MinimalPrototype

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

def PrototypeDecoder
    (c : List DisplayAlphabet) : PrototypeDecoderOutput -> Prop
  | PrototypeDecoderOutput.decoded S => Decodes c S
  | PrototypeDecoderOutput.rejected report => report.stream = c

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

end BEDC.GroundCompiler.MinimalPrototype
