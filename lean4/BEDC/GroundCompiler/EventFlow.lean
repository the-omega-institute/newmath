import BEDC.FKernel.Mark

namespace BEDC.GroundCompiler.EventFlow

open BEDC.FKernel.Mark

def RawEvent : Type := List BMark

def EventFlow : Type := List RawEvent

def EventBoundary (S : EventFlow) (i : Nat) : Prop :=
  i + 1 < S.length

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

theorem input_not_bare_bitstream (decode : List BMark -> EventFlow) :
    Not (forall S : EventFlow, decode (erase S) = S) := by
  intro h
  have hS1 :
      decode (erase [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0]]) =
      [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0]] :=
    h [[BMark.b0], [BMark.b0, BMark.b0],
      [BMark.b0, BMark.b0, BMark.b0]]
  have hS2 :
      decode (erase [[BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0]]) =
      [[BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0]] :=
    h [[BMark.b0, BMark.b0],
      [BMark.b0, BMark.b0, BMark.b0, BMark.b0]]
  have eqFlows :
      [[BMark.b0], [BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0]] =
      [[BMark.b0, BMark.b0],
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0]] :=
    Eq.trans (Eq.symm hS1) hS2
  cases eqFlows

end BEDC.GroundCompiler.EventFlow
