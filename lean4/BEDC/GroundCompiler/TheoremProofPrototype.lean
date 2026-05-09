import BEDC.GroundCompiler.TheoremGenerated

namespace BEDC.GroundCompiler.TheoremProofPrototype

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.TheoremGenerated

def StatementCandidate (S Phi : EventFlow) : Prop :=
  TheoremSourceSubflow Phi S

def GeneratedStatementRecognizer : Type :=
  GeneratedRecognizer

def RecognizesStatement
    (R : GeneratedStatementRecognizer) (S Phi : EventFlow) : Prop :=
  StatementCandidate S Phi /\
    NonemptyEventFlow Phi /\
    Recognizes R S Phi

def RecognizedStatementFlow
    (R : GeneratedStatementRecognizer) (S Phi : EventFlow) : Prop :=
  RecognizesStatement R S Phi

end BEDC.GroundCompiler.TheoremProofPrototype
