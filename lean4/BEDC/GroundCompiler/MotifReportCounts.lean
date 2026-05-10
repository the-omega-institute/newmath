import BEDC.GroundCompiler.SemanticMotif

namespace BEDC.GroundCompiler.MotifReportCounts

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.SemanticMotif

inductive MotifCountStatus : Type where
  | undefined
  | count (n : Nat)

def MotifCountP3
    (_S : EventFlow) (_mu : MotifRole)
    (recognized : Option (List MotifProfileItem)) : MotifCountStatus :=
  match recognized with
  | none => MotifCountStatus.undefined
  | some items => MotifCountStatus.count items.length

def CandidateMotifCount (candidates : List EventFlow) : Nat :=
  candidates.length

theorem candidate_recognized_count_differ :
    exists S mu : EventFlow, exists candidates : List EventFlow,
      CandidateMotifCount candidates = 1 /\
        MotifCountP3 S mu none = MotifCountStatus.undefined /\
        Not
          (MotifCountP3 S mu none =
            MotifCountStatus.count (CandidateMotifCount candidates)) := by
  refine ⟨[], CarryRole, [[]], rfl, rfl, ?_⟩
  intro h
  cases h

theorem missing_recognizer_not_zero {S : EventFlow} {mu : MotifRole} :
    MotifCountP3 S mu none = MotifCountStatus.undefined /\
      Not (MotifCountP3 S mu none = MotifCountStatus.count 0) := by
  constructor
  · rfl
  · intro h
    cases h

end BEDC.GroundCompiler.MotifReportCounts
