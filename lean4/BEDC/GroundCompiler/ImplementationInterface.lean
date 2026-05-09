import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.ImplementationInterface

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
  | recognizesPkg
  | recognizesNameCert
  | recognizesDerivCert
  | recognizesTheorem
  | recognizesChapter
  | recognizesCompiler
  | acceptFlow

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

end BEDC.GroundCompiler.ImplementationInterface
