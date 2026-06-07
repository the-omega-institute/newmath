import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionAdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionAdjunctionUp : Type where
  | mk (X M D U K T R E H C P N : BHist) : MetricCompletionAdjunctionUp
  deriving DecidableEq

def metricCompletionAdjunctionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionAdjunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionAdjunctionEncodeBHist h

def metricCompletionAdjunctionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionAdjunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionAdjunctionDecodeBHist tail)

private theorem metricCompletionAdjunction_decode_encode_bhist :
    forall h : BHist, metricCompletionAdjunctionDecodeBHist
      (metricCompletionAdjunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionAdjunctionFields :
    MetricCompletionAdjunctionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionAdjunctionUp.mk X M D U K T R E H C P N =>
      [X, M, D, U, K, T, R, E, H, C, P, N]

def metricCompletionAdjunctionToEventFlow :
    MetricCompletionAdjunctionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionAdjunctionFields x).map metricCompletionAdjunctionEncodeBHist

private def metricCompletionAdjunctionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionAdjunctionEventAtDefault index rest

def metricCompletionAdjunctionFromEventFlow :
    EventFlow -> Option MetricCompletionAdjunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricCompletionAdjunctionUp.mk
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 0 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 1 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 2 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 3 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 4 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 5 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 6 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 7 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 8 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 9 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 10 ef))
        (metricCompletionAdjunctionDecodeBHist
          (metricCompletionAdjunctionEventAtDefault 11 ef)))

private theorem metricCompletionAdjunction_round_trip :
    forall x : MetricCompletionAdjunctionUp,
      metricCompletionAdjunctionFromEventFlow
        (metricCompletionAdjunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M D U K T R E H C P N =>
      change
        some
          (MetricCompletionAdjunctionUp.mk
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist X))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist M))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist D))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist U))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist K))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist T))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist R))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist E))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist H))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist C))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist P))
            (metricCompletionAdjunctionDecodeBHist
              (metricCompletionAdjunctionEncodeBHist N))) =
          some (MetricCompletionAdjunctionUp.mk X M D U K T R E H C P N)
      rw [metricCompletionAdjunction_decode_encode_bhist X,
        metricCompletionAdjunction_decode_encode_bhist M,
        metricCompletionAdjunction_decode_encode_bhist D,
        metricCompletionAdjunction_decode_encode_bhist U,
        metricCompletionAdjunction_decode_encode_bhist K,
        metricCompletionAdjunction_decode_encode_bhist T,
        metricCompletionAdjunction_decode_encode_bhist R,
        metricCompletionAdjunction_decode_encode_bhist E,
        metricCompletionAdjunction_decode_encode_bhist H,
        metricCompletionAdjunction_decode_encode_bhist C,
        metricCompletionAdjunction_decode_encode_bhist P,
        metricCompletionAdjunction_decode_encode_bhist N]

private theorem metricCompletionAdjunctionToEventFlow_injective
    {x y : MetricCompletionAdjunctionUp} :
    metricCompletionAdjunctionToEventFlow x =
        metricCompletionAdjunctionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionAdjunctionFromEventFlow (metricCompletionAdjunctionToEventFlow x) =
        metricCompletionAdjunctionFromEventFlow (metricCompletionAdjunctionToEventFlow y) :=
    congrArg metricCompletionAdjunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricCompletionAdjunction_round_trip x).symm
      (Eq.trans hread (metricCompletionAdjunction_round_trip y)))

instance metricCompletionAdjunctionBHistCarrier :
    BHistCarrier MetricCompletionAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionAdjunctionToEventFlow
  fromEventFlow := metricCompletionAdjunctionFromEventFlow

instance metricCompletionAdjunctionChapterTasteGate :
    ChapterTasteGate MetricCompletionAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionAdjunctionFromEventFlow
        (metricCompletionAdjunctionToEventFlow x) = some x
    exact metricCompletionAdjunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCompletionAdjunctionToEventFlow_injective heq)

theorem MetricCompletionAdjunctionTasteGate_single_carrier_alignment :
    (forall h : BHist, metricCompletionAdjunctionDecodeBHist
      (metricCompletionAdjunctionEncodeBHist h) = h) ∧
      (forall x : MetricCompletionAdjunctionUp,
        metricCompletionAdjunctionFromEventFlow
          (metricCompletionAdjunctionToEventFlow x) = some x) ∧
        (forall x y : MetricCompletionAdjunctionUp,
          metricCompletionAdjunctionToEventFlow x =
              metricCompletionAdjunctionToEventFlow y ->
            x = y) ∧
          metricCompletionAdjunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨metricCompletionAdjunction_decode_encode_bhist,
      metricCompletionAdjunction_round_trip,
      (fun _ _ heq => metricCompletionAdjunctionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionAdjunctionUp
