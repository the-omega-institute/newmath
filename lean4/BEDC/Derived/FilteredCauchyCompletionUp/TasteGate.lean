import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilteredCauchyCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilteredCauchyCompletionUp : Type where
  | mk
      (filter uniformCriterion sequenceSpace completionRoute realSeal transport continuation
        provenance name : BHist) :
      FilteredCauchyCompletionUp
  deriving DecidableEq

def filteredCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filteredCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filteredCauchyCompletionEncodeBHist h

def filteredCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filteredCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filteredCauchyCompletionDecodeBHist tail)

private theorem filteredCauchyCompletion_decode_encode_bhist :
    ∀ h : BHist,
      filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filteredCauchyCompletionFields : FilteredCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilteredCauchyCompletionUp.mk filter uniformCriterion sequenceSpace completionRoute realSeal
      transport continuation provenance name =>
      [filter, uniformCriterion, sequenceSpace, completionRoute, realSeal, transport,
        continuation, provenance, name]

def filteredCauchyCompletionToEventFlow : FilteredCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (filteredCauchyCompletionFields x).map filteredCauchyCompletionEncodeBHist

private def filteredCauchyCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filteredCauchyCompletionEventAtDefault index rest

def filteredCauchyCompletionFromEventFlow
    (ef : EventFlow) : Option FilteredCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilteredCauchyCompletionUp.mk
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 0 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 1 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 2 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 3 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 4 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 5 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 6 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 7 ef))
      (filteredCauchyCompletionDecodeBHist (filteredCauchyCompletionEventAtDefault 8 ef)))

private theorem filteredCauchyCompletion_round_trip :
    ∀ x : FilteredCauchyCompletionUp,
      filteredCauchyCompletionFromEventFlow (filteredCauchyCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk filter uniformCriterion sequenceSpace completionRoute realSeal transport continuation
      provenance name =>
      change
        some
          (FilteredCauchyCompletionUp.mk
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist filter))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist uniformCriterion))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist sequenceSpace))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist completionRoute))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist realSeal))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist transport))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist continuation))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist provenance))
            (filteredCauchyCompletionDecodeBHist
              (filteredCauchyCompletionEncodeBHist name))) =
          some
            (FilteredCauchyCompletionUp.mk filter uniformCriterion sequenceSpace
              completionRoute realSeal transport continuation provenance name)
      rw [filteredCauchyCompletion_decode_encode_bhist filter,
        filteredCauchyCompletion_decode_encode_bhist uniformCriterion,
        filteredCauchyCompletion_decode_encode_bhist sequenceSpace,
        filteredCauchyCompletion_decode_encode_bhist completionRoute,
        filteredCauchyCompletion_decode_encode_bhist realSeal,
        filteredCauchyCompletion_decode_encode_bhist transport,
        filteredCauchyCompletion_decode_encode_bhist continuation,
        filteredCauchyCompletion_decode_encode_bhist provenance,
        filteredCauchyCompletion_decode_encode_bhist name]

private theorem filteredCauchyCompletionToEventFlow_injective
    {x y : FilteredCauchyCompletionUp} :
    filteredCauchyCompletionToEventFlow x = filteredCauchyCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filteredCauchyCompletionFromEventFlow (filteredCauchyCompletionToEventFlow x) =
        filteredCauchyCompletionFromEventFlow (filteredCauchyCompletionToEventFlow y) :=
    congrArg filteredCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (filteredCauchyCompletion_round_trip x).symm
      (Eq.trans hread (filteredCauchyCompletion_round_trip y)))

instance filteredCauchyCompletionBHistCarrier : BHistCarrier FilteredCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filteredCauchyCompletionToEventFlow
  fromEventFlow := filteredCauchyCompletionFromEventFlow

instance filteredCauchyCompletionChapterTasteGate :
    ChapterTasteGate FilteredCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change filteredCauchyCompletionFromEventFlow (filteredCauchyCompletionToEventFlow x) =
      some x
    exact filteredCauchyCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (filteredCauchyCompletionToEventFlow_injective heq)

theorem FilteredCauchyCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FilteredCauchyCompletionUp) ∧
      Nonempty (ChapterTasteGate FilteredCauchyCompletionUp) ∧
        ∃ x : FilteredCauchyCompletionUp,
          BHistCarrier.toEventFlow x =
            filteredCauchyCompletionToEventFlow
              (FilteredCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨filteredCauchyCompletionBHistCarrier⟩,
      ⟨⟨filteredCauchyCompletionChapterTasteGate⟩,
        ⟨FilteredCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          rfl⟩⟩⟩

end BEDC.Derived.FilteredCauchyCompletionUp.TasteGate
