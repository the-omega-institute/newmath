import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricSequentialCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricSequentialCompletionUp : Type where
  | mk (Q M C W T R E H K P N : BHist) : MetricSequentialCompletionUp
  deriving DecidableEq

def metricSequentialCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricSequentialCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricSequentialCompletionEncodeBHist h

def metricSequentialCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricSequentialCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricSequentialCompletionDecodeBHist tail)

private theorem metricSequentialCompletion_decode_encode_bhist :
    ∀ h : BHist, metricSequentialCompletionDecodeBHist
      (metricSequentialCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricSequentialCompletionFields : MetricSequentialCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricSequentialCompletionUp.mk Q M C W T R E H K P N =>
      [Q, M, C, W, T, R, E, H, K, P, N]

def metricSequentialCompletionToEventFlow : MetricSequentialCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricSequentialCompletionFields x).map metricSequentialCompletionEncodeBHist

private def metricSequentialCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricSequentialCompletionEventAtDefault index rest

def metricSequentialCompletionFromEventFlow : EventFlow → Option MetricSequentialCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricSequentialCompletionUp.mk
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 0 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 1 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 2 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 3 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 4 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 5 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 6 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 7 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 8 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 9 ef))
        (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEventAtDefault 10 ef)))

private theorem metricSequentialCompletion_round_trip :
    ∀ x : MetricSequentialCompletionUp,
      metricSequentialCompletionFromEventFlow
        (metricSequentialCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q M C W T R E H K P N =>
      change
        some
          (MetricSequentialCompletionUp.mk
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist Q))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist M))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist C))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist W))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist T))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist R))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist E))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist H))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist K))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist P))
            (metricSequentialCompletionDecodeBHist (metricSequentialCompletionEncodeBHist N))) =
          some (MetricSequentialCompletionUp.mk Q M C W T R E H K P N)
      rw [metricSequentialCompletion_decode_encode_bhist Q,
        metricSequentialCompletion_decode_encode_bhist M,
        metricSequentialCompletion_decode_encode_bhist C,
        metricSequentialCompletion_decode_encode_bhist W,
        metricSequentialCompletion_decode_encode_bhist T,
        metricSequentialCompletion_decode_encode_bhist R,
        metricSequentialCompletion_decode_encode_bhist E,
        metricSequentialCompletion_decode_encode_bhist H,
        metricSequentialCompletion_decode_encode_bhist K,
        metricSequentialCompletion_decode_encode_bhist P,
        metricSequentialCompletion_decode_encode_bhist N]

private theorem metricSequentialCompletionToEventFlow_injective
    {x y : MetricSequentialCompletionUp} :
    metricSequentialCompletionToEventFlow x = metricSequentialCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricSequentialCompletionFromEventFlow (metricSequentialCompletionToEventFlow x) =
        metricSequentialCompletionFromEventFlow (metricSequentialCompletionToEventFlow y) :=
    congrArg metricSequentialCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricSequentialCompletion_round_trip x).symm
      (Eq.trans hread (metricSequentialCompletion_round_trip y)))

instance metricSequentialCompletionBHistCarrier : BHistCarrier MetricSequentialCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricSequentialCompletionToEventFlow
  fromEventFlow := metricSequentialCompletionFromEventFlow

instance metricSequentialCompletionChapterTasteGate :
    ChapterTasteGate MetricSequentialCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricSequentialCompletionFromEventFlow
      (metricSequentialCompletionToEventFlow x) = some x
    exact metricSequentialCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricSequentialCompletionToEventFlow_injective heq)

theorem MetricSequentialCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricSequentialCompletionDecodeBHist
      (metricSequentialCompletionEncodeBHist h) = h) ∧
      (∀ x : MetricSequentialCompletionUp,
        metricSequentialCompletionFromEventFlow
          (metricSequentialCompletionToEventFlow x) = some x) ∧
        (∀ x y : MetricSequentialCompletionUp,
          metricSequentialCompletionToEventFlow x = metricSequentialCompletionToEventFlow y →
            x = y) ∧
          metricSequentialCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨metricSequentialCompletion_decode_encode_bhist,
      metricSequentialCompletion_round_trip,
      (fun _ _ heq => metricSequentialCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricSequentialCompletionUp
