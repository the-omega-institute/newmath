import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionLadderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionLadderUp : Type where
  | mk (D W R E S U H C P N : BHist) : CompletionLadderUp
  deriving DecidableEq

def completionLadderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionLadderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionLadderEncodeBHist h

def completionLadderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionLadderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionLadderDecodeBHist tail)

private theorem CompletionLadderTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, completionLadderDecodeBHist (completionLadderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionLadderFields : CompletionLadderUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionLadderUp.mk D W R E S U H C P N => [D, W, R, E, S, U, H, C, P, N]

def completionLadderToEventFlow : CompletionLadderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionLadderFields x).map completionLadderEncodeBHist

private def completionLadderEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionLadderEventAt index rest

def completionLadderFromEventFlow (flow : EventFlow) : Option CompletionLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionLadderUp.mk
      (completionLadderDecodeBHist (completionLadderEventAt 0 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 1 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 2 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 3 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 4 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 5 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 6 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 7 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 8 flow))
      (completionLadderDecodeBHist (completionLadderEventAt 9 flow)))

private theorem CompletionLadderTasteGate_single_carrier_alignment_round_trip :
    forall x : CompletionLadderUp,
      completionLadderFromEventFlow (completionLadderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R E S U H C P N =>
      change
        some
          (CompletionLadderUp.mk
            (completionLadderDecodeBHist (completionLadderEncodeBHist D))
            (completionLadderDecodeBHist (completionLadderEncodeBHist W))
            (completionLadderDecodeBHist (completionLadderEncodeBHist R))
            (completionLadderDecodeBHist (completionLadderEncodeBHist E))
            (completionLadderDecodeBHist (completionLadderEncodeBHist S))
            (completionLadderDecodeBHist (completionLadderEncodeBHist U))
            (completionLadderDecodeBHist (completionLadderEncodeBHist H))
            (completionLadderDecodeBHist (completionLadderEncodeBHist C))
            (completionLadderDecodeBHist (completionLadderEncodeBHist P))
            (completionLadderDecodeBHist (completionLadderEncodeBHist N))) =
          some (CompletionLadderUp.mk D W R E S U H C P N)
      rw [CompletionLadderTasteGate_single_carrier_alignment_decode_encode D,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode W,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode R,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode E,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode S,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode U,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode H,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode C,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode P,
        CompletionLadderTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompletionLadderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionLadderUp} :
    completionLadderToEventFlow x = completionLadderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionLadderFromEventFlow (completionLadderToEventFlow x) =
        completionLadderFromEventFlow (completionLadderToEventFlow y) :=
    congrArg completionLadderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionLadderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompletionLadderTasteGate_single_carrier_alignment_round_trip y)))

instance completionLadderBHistCarrier : BHistCarrier CompletionLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionLadderToEventFlow
  fromEventFlow := completionLadderFromEventFlow

instance completionLadderChapterTasteGate : ChapterTasteGate CompletionLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionLadderFromEventFlow (completionLadderToEventFlow x) = some x
    exact CompletionLadderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionLadderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompletionLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionLadderChapterTasteGate

theorem CompletionLadderTasteGate_single_carrier_alignment :
    (forall h : BHist, completionLadderDecodeBHist (completionLadderEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompletionLadderUp) ∧
        Nonempty (ChapterTasteGate CompletionLadderUp) ∧
          completionLadderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CompletionLadderTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨completionLadderBHistCarrier⟩
    · constructor
      · exact ⟨completionLadderChapterTasteGate⟩
      · rfl

end BEDC.Derived.CompletionLadderUp
