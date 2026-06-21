import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentiallyCompactCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentiallyCompactCompletionUp : Type where
  | mk (T S K W R E H C P N : BHist) : SequentiallyCompactCompletionUp
  deriving DecidableEq

def sequentiallyCompactCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentiallyCompactCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentiallyCompactCompletionEncodeBHist h

def sequentiallyCompactCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentiallyCompactCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentiallyCompactCompletionDecodeBHist tail)

private theorem SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentiallyCompactCompletionFields :
    SequentiallyCompactCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentiallyCompactCompletionUp.mk T S K W R E H C P N =>
      [T, S, K, W, R, E, H, C, P, N]

def sequentiallyCompactCompletionToEventFlow :
    SequentiallyCompactCompletionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (sequentiallyCompactCompletionFields x).map
      sequentiallyCompactCompletionEncodeBHist

private def sequentiallyCompactCompletionEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      sequentiallyCompactCompletionEventAtDefault index rest

def sequentiallyCompactCompletionFromEventFlow
    (ef : EventFlow) : Option SequentiallyCompactCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentiallyCompactCompletionUp.mk
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 0 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 1 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 2 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 3 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 4 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 5 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 6 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 7 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 8 ef))
      (sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEventAtDefault 9 ef)))

private theorem SequentiallyCompactCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : SequentiallyCompactCompletionUp,
      sequentiallyCompactCompletionFromEventFlow
        (sequentiallyCompactCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk T S K W R E H C P N =>
      change
        some
          (SequentiallyCompactCompletionUp.mk
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist T))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist S))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist K))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist W))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist R))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist E))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist H))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist C))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist P))
            (sequentiallyCompactCompletionDecodeBHist
              (sequentiallyCompactCompletionEncodeBHist N))) =
          some (SequentiallyCompactCompletionUp.mk T S K W R E H C P N)
      rw [
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode T,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode S,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode K,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode W,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode R,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode E,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode H,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode C,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode P,
        SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode N]

private theorem SequentiallyCompactCompletionTasteGate_single_carrier_alignment_injective
    {x y : SequentiallyCompactCompletionUp} :
    sequentiallyCompactCompletionToEventFlow x =
        sequentiallyCompactCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentiallyCompactCompletionFromEventFlow
          (sequentiallyCompactCompletionToEventFlow x) =
        sequentiallyCompactCompletionFromEventFlow
          (sequentiallyCompactCompletionToEventFlow y) :=
    congrArg sequentiallyCompactCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SequentiallyCompactCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentiallyCompactCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance sequentiallyCompactCompletionBHistCarrier :
    BHistCarrier SequentiallyCompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentiallyCompactCompletionToEventFlow
  fromEventFlow := sequentiallyCompactCompletionFromEventFlow

instance sequentiallyCompactCompletionChapterTasteGate :
    ChapterTasteGate SequentiallyCompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentiallyCompactCompletionFromEventFlow
        (sequentiallyCompactCompletionToEventFlow x) = some x
    exact SequentiallyCompactCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentiallyCompactCompletionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SequentiallyCompactCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentiallyCompactCompletionChapterTasteGate

theorem SequentiallyCompactCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      sequentiallyCompactCompletionDecodeBHist
        (sequentiallyCompactCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SequentiallyCompactCompletionUp) ∧
      Nonempty (ChapterTasteGate SequentiallyCompactCompletionUp) ∧
      sequentiallyCompactCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SequentiallyCompactCompletionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨sequentiallyCompactCompletionBHistCarrier⟩
    · constructor
      · exact ⟨sequentiallyCompactCompletionChapterTasteGate⟩
      · rfl

end BEDC.Derived.SequentiallyCompactCompletionUp
