import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.ImplementationInterface

open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

inductive InterfaceDatum : Type where
  | hostBoolList
  | hostBitArray
  | hostString
  | hostVector
  | hostParserState
  | hostJsonObject
  | hostLeanStructure
  | hostRustStruct
  | hostPythonDataclass
  | isRawEvent
  | isEventFlow
  | isLegalZStream
  | encodesEvent
  | compiles
  | decodes
  | rejects
  | recognizes
  | certifiedRecognizer
  | recognizesPkg
  | recognizesNameCert
  | recognizesDerivCert
  | recognizesTheorem
  | recognizesChapter
  | recognizesCompiler
  | acceptFlow
  | motifReport
  | metricReport
  | cannotClaim
  | bridgeObligation

inductive ImplementationRepresentation : InterfaceDatum -> Prop where
  | hostBoolList :
      ImplementationRepresentation InterfaceDatum.hostBoolList
  | hostBitArray :
      ImplementationRepresentation InterfaceDatum.hostBitArray
  | hostString :
      ImplementationRepresentation InterfaceDatum.hostString
  | hostVector :
      ImplementationRepresentation InterfaceDatum.hostVector
  | hostParserState :
      ImplementationRepresentation InterfaceDatum.hostParserState
  | hostJsonObject :
      ImplementationRepresentation InterfaceDatum.hostJsonObject
  | hostLeanStructure :
      ImplementationRepresentation InterfaceDatum.hostLeanStructure
  | hostRustStruct :
      ImplementationRepresentation InterfaceDatum.hostRustStruct
  | hostPythonDataclass :
      ImplementationRepresentation InterfaceDatum.hostPythonDataclass

inductive PublicFormalInterface : InterfaceDatum -> Prop where
  | isRawEvent :
      PublicFormalInterface InterfaceDatum.isRawEvent
  | isEventFlow :
      PublicFormalInterface InterfaceDatum.isEventFlow
  | isLegalZStream :
      PublicFormalInterface InterfaceDatum.isLegalZStream
  | encodesEvent :
      PublicFormalInterface InterfaceDatum.encodesEvent
  | compiles :
      PublicFormalInterface InterfaceDatum.compiles
  | decodes :
      PublicFormalInterface InterfaceDatum.decodes
  | rejects :
      PublicFormalInterface InterfaceDatum.rejects
  | recognizes :
      PublicFormalInterface InterfaceDatum.recognizes
  | certifiedRecognizer :
      PublicFormalInterface InterfaceDatum.certifiedRecognizer
  | recognizesPkg :
      PublicFormalInterface InterfaceDatum.recognizesPkg
  | recognizesNameCert :
      PublicFormalInterface InterfaceDatum.recognizesNameCert
  | recognizesDerivCert :
      PublicFormalInterface InterfaceDatum.recognizesDerivCert
  | recognizesTheorem :
      PublicFormalInterface InterfaceDatum.recognizesTheorem
  | recognizesChapter :
      PublicFormalInterface InterfaceDatum.recognizesChapter
  | recognizesCompiler :
      PublicFormalInterface InterfaceDatum.recognizesCompiler
  | acceptFlow :
      PublicFormalInterface InterfaceDatum.acceptFlow

def ImplementationSoundness {α β : Type}
    (impl formal : α -> β -> Prop) : Prop :=
  forall x y, impl x y -> formal x y

def ImplementationCompleteness {α β : Type}
    (domain : α -> Prop) (impl formal : α -> β -> Prop) : Prop :=
  forall x y, domain x -> formal x y -> impl x y

def NoHostLeakCondition (publicSurface : InterfaceDatum -> Prop) : Prop :=
  forall d, publicSurface d -> Not (ImplementationRepresentation d)

def HostLeak (publicSurface : InterfaceDatum -> Prop) : Prop :=
  exists d, publicSurface d /\ ImplementationRepresentation d

def NoHiddenInputStatus (publicSurface : InterfaceDatum -> Prop) : Prop :=
  NoHostLeakCondition publicSurface

inductive ChannelCorePublic : InterfaceDatum -> Prop where
  | encodesEvent :
      ChannelCorePublic InterfaceDatum.encodesEvent
  | compiles :
      ChannelCorePublic InterfaceDatum.compiles
  | isLegalZStream :
      ChannelCorePublic InterfaceDatum.isLegalZStream

def ChannelCoreModule (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> ChannelCorePublic d) /\
    publicSurface InterfaceDatum.encodesEvent /\
    publicSurface InterfaceDatum.compiles /\
    publicSurface InterfaceDatum.isLegalZStream /\
    NoHostLeakCondition publicSurface

inductive DecoderCorePublic : InterfaceDatum -> Prop where
  | decodes :
      DecoderCorePublic InterfaceDatum.decodes
  | rejects :
      DecoderCorePublic InterfaceDatum.rejects

def DecoderCoreModule (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> DecoderCorePublic d) /\
    publicSurface InterfaceDatum.decodes /\
    publicSurface InterfaceDatum.rejects /\
    NoHostLeakCondition publicSurface

inductive RoundTripPublic : InterfaceDatum -> Prop where
  | compiles :
      RoundTripPublic InterfaceDatum.compiles
  | decodes :
      RoundTripPublic InterfaceDatum.decodes
  | isLegalZStream :
      RoundTripPublic InterfaceDatum.isLegalZStream

def RoundTripModule (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> RoundTripPublic d) /\
    publicSurface InterfaceDatum.compiles /\
    publicSurface InterfaceDatum.decodes /\
    publicSurface InterfaceDatum.isLegalZStream /\
    NoHostLeakCondition publicSurface

inductive LayerSeparationPublic : InterfaceDatum -> Prop where
  | isRawEvent :
      LayerSeparationPublic InterfaceDatum.isRawEvent
  | isEventFlow :
      LayerSeparationPublic InterfaceDatum.isEventFlow
  | isLegalZStream :
      LayerSeparationPublic InterfaceDatum.isLegalZStream
  | encodesEvent :
      LayerSeparationPublic InterfaceDatum.encodesEvent
  | decodes :
      LayerSeparationPublic InterfaceDatum.decodes

def LayerSeparationModule (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> LayerSeparationPublic d) /\
    publicSurface InterfaceDatum.isRawEvent /\
    publicSurface InterfaceDatum.isEventFlow /\
    publicSurface InterfaceDatum.isLegalZStream /\
    publicSurface InterfaceDatum.encodesEvent /\
    publicSurface InterfaceDatum.decodes /\
    NoHostLeakCondition publicSurface

inductive RecognizerCorePublic : InterfaceDatum -> Prop where
  | recognizes :
      RecognizerCorePublic InterfaceDatum.recognizes
  | certifiedRecognizer :
      RecognizerCorePublic InterfaceDatum.certifiedRecognizer

def RecognizerCoreModule (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> RecognizerCorePublic d) /\
    publicSurface InterfaceDatum.recognizes /\
    publicSurface InterfaceDatum.certifiedRecognizer /\
    NoHostLeakCondition publicSurface

inductive CertificateRecognizerPublic : InterfaceDatum -> Prop where
  | recognizesPkg :
      CertificateRecognizerPublic InterfaceDatum.recognizesPkg
  | recognizesNameCert :
      CertificateRecognizerPublic InterfaceDatum.recognizesNameCert
  | recognizesDerivCert :
      CertificateRecognizerPublic InterfaceDatum.recognizesDerivCert
  | acceptFlow :
      CertificateRecognizerPublic InterfaceDatum.acceptFlow
  | recognizesTheorem :
      CertificateRecognizerPublic InterfaceDatum.recognizesTheorem
  | recognizesChapter :
      CertificateRecognizerPublic InterfaceDatum.recognizesChapter
  | recognizesCompiler :
      CertificateRecognizerPublic InterfaceDatum.recognizesCompiler

def CertificateRecognizerModules (publicSurface : InterfaceDatum -> Prop) :
    Prop :=
  (forall d, publicSurface d -> CertificateRecognizerPublic d) /\
    publicSurface InterfaceDatum.recognizesPkg /\
    publicSurface InterfaceDatum.recognizesNameCert /\
    publicSurface InterfaceDatum.recognizesDerivCert /\
    publicSurface InterfaceDatum.acceptFlow /\
    publicSurface InterfaceDatum.recognizesTheorem /\
    publicSurface InterfaceDatum.recognizesChapter /\
    publicSurface InterfaceDatum.recognizesCompiler /\
    NoHostLeakCondition publicSurface

inductive AnalysisPublic : InterfaceDatum -> Prop where
  | motifReport :
      AnalysisPublic InterfaceDatum.motifReport
  | metricReport :
      AnalysisPublic InterfaceDatum.metricReport
  | cannotClaim :
      AnalysisPublic InterfaceDatum.cannotClaim
  | bridgeObligation :
      AnalysisPublic InterfaceDatum.bridgeObligation

def AnalysisModules (publicSurface : InterfaceDatum -> Prop) : Prop :=
  (forall d, publicSurface d -> AnalysisPublic d) /\
    publicSurface InterfaceDatum.motifReport /\
    publicSurface InterfaceDatum.metricReport /\
    publicSurface InterfaceDatum.cannotClaim /\
    publicSurface InterfaceDatum.bridgeObligation /\
    NoHostLeakCondition publicSurface

def DecodesEvent (c : List DisplayAlphabet) (w : RawEvent) : Prop :=
  EncodesEvent w c

def Decodes (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  Compiles S c

inductive DecoderOutcome : Type where
  | decoded (S : EventFlow)
  | rejected (r : EventFlow)

def ExecutableDecoder (c : List DisplayAlphabet) : DecoderOutcome :=
  match Decode c with
  | some S => DecoderOutcome.decoded S
  | none => DecoderOutcome.rejected []

def ExecutableEncoder : EventFlow -> List DisplayAlphabet :=
  FlowEncoding

theorem host_representation_not_structure {d : InterfaceDatum} :
    ImplementationRepresentation d -> Not (PublicFormalInterface d) := by
  intro hImplementation hPublic
  cases hImplementation <;> cases hPublic

theorem host_leak_invalidates {publicSurface : InterfaceDatum -> Prop} :
    HostLeak publicSurface -> Not (NoHiddenInputStatus publicSurface) := by
  intro hLeak hStatus
  cases hLeak with
  | intro d hd =>
      exact hStatus d hd.left hd.right

theorem decoder_functional {c : List DisplayAlphabet} {S T : EventFlow} :
    Decodes c S -> Decodes c T -> S = T := by
  intro hS hT
  have hDecodeS : Decode c = some S := by
    rw [hS]
    exact flow_level_round_trip S
  have hDecodeT : Decode c = some T := by
    rw [hT]
    exact flow_level_round_trip T
  rw [hDecodeS] at hDecodeT
  cases hDecodeT
  rfl

theorem encoder_soundness_obligation {S : EventFlow}
    {c : List DisplayAlphabet} :
    ExecutableEncoder S = c -> Compiles S c := by
  intro h
  exact h.symm

theorem encoder_totality_obligation (S : EventFlow) :
    exists c : List DisplayAlphabet, ExecutableEncoder S = c /\ Compiles S c := by
  exact ⟨FlowEncoding S, rfl, rfl⟩

end BEDC.GroundCompiler.ImplementationInterface
