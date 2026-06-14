import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DistanceFunctionCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DistanceFunctionCompletionUp : Type where
  | mk (M C K S R D A H T P N : BHist) : DistanceFunctionCompletionUp
  deriving DecidableEq

def distanceFunctionCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: distanceFunctionCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: distanceFunctionCompletionEncodeBHist h

def distanceFunctionCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (distanceFunctionCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (distanceFunctionCompletionDecodeBHist tail)

private theorem DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      distanceFunctionCompletionDecodeBHist
        (distanceFunctionCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def distanceFunctionCompletionFields :
    DistanceFunctionCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DistanceFunctionCompletionUp.mk M C K S R D A H T P N =>
      [M, C, K, S, R, D, A, H, T, P, N]

def distanceFunctionCompletionToEventFlow :
    DistanceFunctionCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (distanceFunctionCompletionFields x).map distanceFunctionCompletionEncodeBHist

private def distanceFunctionCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => distanceFunctionCompletionEventAt index rest

def distanceFunctionCompletionFromEventFlow
    (ef : EventFlow) : Option DistanceFunctionCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DistanceFunctionCompletionUp.mk
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 0 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 1 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 2 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 3 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 4 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 5 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 6 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 7 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 8 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 9 ef))
      (distanceFunctionCompletionDecodeBHist (distanceFunctionCompletionEventAt 10 ef)))

private theorem DistanceFunctionCompletionTasteGate_single_carrier_alignment_round_trip
    (x : DistanceFunctionCompletionUp) :
    distanceFunctionCompletionFromEventFlow
        (distanceFunctionCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M C K S R D A H T P N =>
      change
        some
            (DistanceFunctionCompletionUp.mk
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist M))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist C))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist K))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist S))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist R))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist D))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist A))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist H))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist T))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist P))
              (distanceFunctionCompletionDecodeBHist
                (distanceFunctionCompletionEncodeBHist N))) =
          some (DistanceFunctionCompletionUp.mk M C K S R D A H T P N)
      rw [DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode M,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode C,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode K,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode S,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode R,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode D,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode A,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode H,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode T,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode P,
        DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DistanceFunctionCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DistanceFunctionCompletionUp} :
    distanceFunctionCompletionToEventFlow x =
        distanceFunctionCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      distanceFunctionCompletionFromEventFlow
          (distanceFunctionCompletionToEventFlow x) =
        distanceFunctionCompletionFromEventFlow
          (distanceFunctionCompletionToEventFlow y) :=
    congrArg distanceFunctionCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DistanceFunctionCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DistanceFunctionCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance distanceFunctionCompletionBHistCarrier :
    BHistCarrier DistanceFunctionCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := distanceFunctionCompletionToEventFlow
  fromEventFlow := distanceFunctionCompletionFromEventFlow

instance distanceFunctionCompletionChapterTasteGate :
    ChapterTasteGate DistanceFunctionCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      distanceFunctionCompletionFromEventFlow
        (distanceFunctionCompletionToEventFlow x) = some x
    exact DistanceFunctionCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DistanceFunctionCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate DistanceFunctionCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  distanceFunctionCompletionChapterTasteGate

theorem DistanceFunctionCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      distanceFunctionCompletionDecodeBHist
        (distanceFunctionCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DistanceFunctionCompletionUp) ∧
        Nonempty (ChapterTasteGate DistanceFunctionCompletionUp) ∧
          distanceFunctionCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DistanceFunctionCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨distanceFunctionCompletionBHistCarrier⟩,
      ⟨distanceFunctionCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.DistanceFunctionCompletionUp
