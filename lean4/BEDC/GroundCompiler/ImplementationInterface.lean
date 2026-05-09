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
  | compiles
  | decodes
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
  | compiles :
      PublicFormalInterface InterfaceDatum.compiles
  | decodes :
      PublicFormalInterface InterfaceDatum.decodes
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

theorem host_representation_not_structure {d : InterfaceDatum} :
    ImplementationRepresentation d -> Not (PublicFormalInterface d) := by
  intro hImplementation hPublic
  cases hImplementation <;> cases hPublic

end BEDC.GroundCompiler.ImplementationInterface
