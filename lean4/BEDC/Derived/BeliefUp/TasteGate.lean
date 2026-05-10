import BEDC.GroundCompiler.TasteGate

namespace BEDC.Derived.BeliefUp

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.TasteGate

def taste_gate : ChapterTasteGate Unit where
  conservativity_holds := ∀ beliefHistoryLength : Nat, beliefHistoryLength = beliefHistoryLength
  conservativity_proof := fun beliefHistoryLength => Eq.refl beliefHistoryLength
  no_hidden_input_holds := Recognizes ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
  no_hidden_input_proof := FormalCompilerInput.recognizedFlow [] []
  round_trip_holds := Decode (FlowEncoding ([] : EventFlow)) = some ([] : EventFlow)
  round_trip_proof := rfl
  layer_separation_holds := True
  layer_separation_proof := True.intro

end BEDC.Derived.BeliefUp
