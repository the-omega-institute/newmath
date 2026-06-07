import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalCompletionUp : Type where
  | mk (L N D W R E H C P Q : BHist) : RealIntervalCompletionUp
  deriving DecidableEq

def realIntervalCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalCompletionEncodeBHist h

def realIntervalCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalCompletionDecodeBHist tail)

private theorem realIntervalCompletion_decode_encode :
    ∀ h : BHist,
      realIntervalCompletionDecodeBHist
          (realIntervalCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalCompletionFields : RealIntervalCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalCompletionUp.mk L N D W R E H C P Q =>
      [L, N, D, W, R, E, H, C, P, Q]

def realIntervalCompletionToEventFlow : RealIntervalCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map realIntervalCompletionEncodeBHist
        (realIntervalCompletionFields x)

private def realIntervalCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realIntervalCompletionRawAt index rest

def realIntervalCompletionFromEventFlow
    (flow : EventFlow) : Option RealIntervalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalCompletionUp.mk
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 0 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 1 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 2 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 3 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 4 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 5 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 6 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 7 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 8 flow))
      (realIntervalCompletionDecodeBHist (realIntervalCompletionRawAt 9 flow)))

private theorem realIntervalCompletion_round_trip :
    ∀ x : RealIntervalCompletionUp,
      realIntervalCompletionFromEventFlow
          (realIntervalCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L N D W R E H C P Q =>
      change
        some
          (RealIntervalCompletionUp.mk
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist L))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist N))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist D))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist W))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist R))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist E))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist H))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist C))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist P))
            (realIntervalCompletionDecodeBHist (realIntervalCompletionEncodeBHist Q))) =
          some (RealIntervalCompletionUp.mk L N D W R E H C P Q)
      rw [realIntervalCompletion_decode_encode L,
        realIntervalCompletion_decode_encode N,
        realIntervalCompletion_decode_encode D,
        realIntervalCompletion_decode_encode W,
        realIntervalCompletion_decode_encode R,
        realIntervalCompletion_decode_encode E,
        realIntervalCompletion_decode_encode H,
        realIntervalCompletion_decode_encode C,
        realIntervalCompletion_decode_encode P,
        realIntervalCompletion_decode_encode Q]

private theorem realIntervalCompletionToEventFlow_injective
    {x y : RealIntervalCompletionUp} :
    realIntervalCompletionToEventFlow x =
        realIntervalCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalCompletionFromEventFlow
          (realIntervalCompletionToEventFlow x) =
        realIntervalCompletionFromEventFlow
          (realIntervalCompletionToEventFlow y) :=
    congrArg realIntervalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realIntervalCompletion_round_trip x).symm
      (Eq.trans hread (realIntervalCompletion_round_trip y)))

instance realIntervalCompletionBHistCarrier :
    BHistCarrier RealIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalCompletionToEventFlow
  fromEventFlow := realIntervalCompletionFromEventFlow

instance realIntervalCompletionChapterTasteGate :
    ChapterTasteGate RealIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalCompletionFromEventFlow (realIntervalCompletionToEventFlow x) = some x
    exact realIntervalCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realIntervalCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealIntervalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntervalCompletionChapterTasteGate

theorem RealIntervalCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realIntervalCompletionDecodeBHist
          (realIntervalCompletionEncodeBHist h) =
        h) ∧
      (∀ x : RealIntervalCompletionUp,
        realIntervalCompletionFromEventFlow
            (realIntervalCompletionToEventFlow x) =
          some x) ∧
        (∀ x y : RealIntervalCompletionUp,
          realIntervalCompletionToEventFlow x =
              realIntervalCompletionToEventFlow y →
            x = y) ∧
          realIntervalCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realIntervalCompletion_decode_encode,
      realIntervalCompletion_round_trip,
      by
        intro x y heq
        exact realIntervalCompletionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealIntervalCompletionUp
