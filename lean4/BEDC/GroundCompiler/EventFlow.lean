import BEDC.FKernel.Mark

namespace BEDC.GroundCompiler.EventFlow

open BEDC.FKernel.Mark

def RawEvent : Type := List BMark

def EventFlow : Type := List RawEvent

def erase (S : EventFlow) : List BMark :=
  S.flatten

theorem erase_not_injective :
    exists S1 S2 : EventFlow, Not (S1 = S2) /\ erase S1 = erase S2 := by
  refine
    ⟨[[BMark.b0], [BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b0]],
      [[BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b0, BMark.b0]], ?_⟩
  constructor
  · intro h
    cases h
  · rfl

end BEDC.GroundCompiler.EventFlow
