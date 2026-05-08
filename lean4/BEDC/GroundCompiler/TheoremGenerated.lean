import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.TheoremGenerated

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def TheoremCandidateFlow : Type :=
  EventFlow

def GeneratedTheoremRecognizer : Type :=
  GeneratedRecognizer

def TheoremRecognitionRelation
    (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  RecognizesTheorem R T

def TheoremFlow (T : TheoremCandidateFlow) : Prop :=
  exists R : GeneratedTheoremRecognizer, TheoremRecognitionRelation R T

def TheoremCode (T : TheoremCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding T

theorem theorem_recognition_preserves_code
    {R : GeneratedTheoremRecognizer} {T : TheoremCandidateFlow} :
    TheoremRecognitionRelation R T -> TheoremCode T = FlowEncoding T := by
  intro _
  rfl

end BEDC.GroundCompiler.TheoremGenerated
