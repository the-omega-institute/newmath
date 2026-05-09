import BEDC.GroundCompiler.ImplementationInterface

namespace BEDC.GroundCompiler.MinimalPrototype

open BEDC.GroundCompiler.ImplementationInterface

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

end BEDC.GroundCompiler.MinimalPrototype
