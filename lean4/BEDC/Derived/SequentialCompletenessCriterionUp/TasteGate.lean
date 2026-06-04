import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCompletenessCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCompletenessCriterionUp : Type where
  | mk (S C R M W G E H T P N : BHist) : SequentialCompletenessCriterionUp
  deriving DecidableEq

def sequentialCompletenessCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCompletenessCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCompletenessCriterionEncodeBHist h

def sequentialCompletenessCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCompletenessCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCompletenessCriterionDecodeBHist tail)

private theorem sequentialCompletenessCriterion_decode_encode :
    ∀ h : BHist,
      sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sequentialCompletenessCriterionFields :
    SequentialCompletenessCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCompletenessCriterionUp.mk S C R M W G E H T P N =>
      [S, C, R, M, W, G, E, H, T, P, N]

def sequentialCompletenessCriterionToEventFlow :
    SequentialCompletenessCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialCompletenessCriterionFields x).map
      sequentialCompletenessCriterionEncodeBHist

private def sequentialCompletenessCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialCompletenessCriterionEventAt index rest

def sequentialCompletenessCriterionFromEventFlow
    (ef : EventFlow) : Option SequentialCompletenessCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialCompletenessCriterionUp.mk
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 0 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 1 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 2 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 3 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 4 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 5 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 6 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 7 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 8 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 9 ef))
      (sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEventAt 10 ef)))

private theorem SequentialCompletenessCriterionTasteGate_single_carrier_alignment_round_trip
    (x : SequentialCompletenessCriterionUp) :
    sequentialCompletenessCriterionFromEventFlow
        (sequentialCompletenessCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S C R M W G E H T P N =>
      change
        some
            (SequentialCompletenessCriterionUp.mk
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist S))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist C))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist R))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist M))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist W))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist G))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist E))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist H))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist T))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist P))
              (sequentialCompletenessCriterionDecodeBHist
                (sequentialCompletenessCriterionEncodeBHist N))) =
          some (SequentialCompletenessCriterionUp.mk S C R M W G E H T P N)
      rw [sequentialCompletenessCriterion_decode_encode S,
        sequentialCompletenessCriterion_decode_encode C,
        sequentialCompletenessCriterion_decode_encode R,
        sequentialCompletenessCriterion_decode_encode M,
        sequentialCompletenessCriterion_decode_encode W,
        sequentialCompletenessCriterion_decode_encode G,
        sequentialCompletenessCriterion_decode_encode E,
        sequentialCompletenessCriterion_decode_encode H,
        sequentialCompletenessCriterion_decode_encode T,
        sequentialCompletenessCriterion_decode_encode P,
        sequentialCompletenessCriterion_decode_encode N]

private theorem
    SequentialCompletenessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialCompletenessCriterionUp} :
    sequentialCompletenessCriterionToEventFlow x =
        sequentialCompletenessCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCompletenessCriterionFromEventFlow
          (sequentialCompletenessCriterionToEventFlow x) =
        sequentialCompletenessCriterionFromEventFlow
          (sequentialCompletenessCriterionToEventFlow y) :=
    congrArg sequentialCompletenessCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SequentialCompletenessCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentialCompletenessCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance sequentialCompletenessCriterionBHistCarrier :
    BHistCarrier SequentialCompletenessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCompletenessCriterionToEventFlow
  fromEventFlow := sequentialCompletenessCriterionFromEventFlow

instance sequentialCompletenessCriterionChapterTasteGate :
    ChapterTasteGate SequentialCompletenessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentialCompletenessCriterionFromEventFlow
          (sequentialCompletenessCriterionToEventFlow x) = some x
    exact SequentialCompletenessCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentialCompletenessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem SequentialCompletenessCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialCompletenessCriterionDecodeBHist
        (sequentialCompletenessCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SequentialCompletenessCriterionUp) ∧
        Nonempty (ChapterTasteGate SequentialCompletenessCriterionUp) ∧
          sequentialCompletenessCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨sequentialCompletenessCriterion_decode_encode,
      ⟨sequentialCompletenessCriterionBHistCarrier⟩,
      ⟨sequentialCompletenessCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SequentialCompletenessCriterionUp
