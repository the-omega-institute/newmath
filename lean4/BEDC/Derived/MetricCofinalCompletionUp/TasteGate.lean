import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCofinalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCofinalCompletionUp : Type where
  | mk (X F D R S H C P N : BHist) : MetricCofinalCompletionUp
  deriving DecidableEq

def metricCofinalCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCofinalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCofinalCompletionEncodeBHist h

def metricCofinalCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCofinalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCofinalCompletionDecodeBHist tail)

private theorem MetricCofinalCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCofinalCompletionToEventFlow :
    MetricCofinalCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCofinalCompletionUp.mk X F D R S H C P N =>
      [metricCofinalCompletionEncodeBHist X,
        metricCofinalCompletionEncodeBHist F,
        metricCofinalCompletionEncodeBHist D,
        metricCofinalCompletionEncodeBHist R,
        metricCofinalCompletionEncodeBHist S,
        metricCofinalCompletionEncodeBHist H,
        metricCofinalCompletionEncodeBHist C,
        metricCofinalCompletionEncodeBHist P,
        metricCofinalCompletionEncodeBHist N]

private def metricCofinalCompletionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metricCofinalCompletionEventAtDefault index rest

def metricCofinalCompletionFromEventFlow
    (ef : EventFlow) : Option MetricCofinalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCofinalCompletionUp.mk
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 0 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 1 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 2 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 3 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 4 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 5 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 6 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 7 ef))
      (metricCofinalCompletionDecodeBHist
        (metricCofinalCompletionEventAtDefault 8 ef)))

private theorem MetricCofinalCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCofinalCompletionUp,
      metricCofinalCompletionFromEventFlow
        (metricCofinalCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F D R S H C P N =>
      change
        some
          (MetricCofinalCompletionUp.mk
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist X))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist F))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist D))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist R))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist S))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist H))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist C))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist P))
            (metricCofinalCompletionDecodeBHist
              (metricCofinalCompletionEncodeBHist N))) =
          some (MetricCofinalCompletionUp.mk X F D R S H C P N)
      rw [MetricCofinalCompletionTasteGate_single_carrier_alignment_decode X,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode F,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode D,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode R,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode S,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode H,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode C,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode P,
        MetricCofinalCompletionTasteGate_single_carrier_alignment_decode N]

private theorem MetricCofinalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCofinalCompletionUp} :
    metricCofinalCompletionToEventFlow x =
        metricCofinalCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCofinalCompletionFromEventFlow
          (metricCofinalCompletionToEventFlow x) =
        metricCofinalCompletionFromEventFlow
          (metricCofinalCompletionToEventFlow y) :=
    congrArg metricCofinalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCofinalCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCofinalCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance metricCofinalCompletionBHistCarrier :
    BHistCarrier MetricCofinalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCofinalCompletionToEventFlow
  fromEventFlow := metricCofinalCompletionFromEventFlow

instance metricCofinalCompletionChapterTasteGate :
    ChapterTasteGate MetricCofinalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCofinalCompletionFromEventFlow
        (metricCofinalCompletionToEventFlow x) = some x
    exact MetricCofinalCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCofinalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricCofinalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCofinalCompletionChapterTasteGate

theorem MetricCofinalCompletionTasteGate_single_carrier_alignment :
    ChapterTasteGate MetricCofinalCompletionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact metricCofinalCompletionChapterTasteGate

end BEDC.Derived.MetricCofinalCompletionUp
