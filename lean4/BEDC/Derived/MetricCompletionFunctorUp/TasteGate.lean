import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionFunctorUp : Type where
  | mk (M0 M1 G E T H C P N : BHist) : MetricCompletionFunctorUp
  deriving DecidableEq

private def metricCompletionFunctorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionFunctorEncodeBHist h

private def metricCompletionFunctorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionFunctorDecodeBHist tail)

private theorem MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def metricCompletionFunctorFields : MetricCompletionFunctorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionFunctorUp.mk M0 M1 G E T H C P N => [M0, M1, G, E, T, H, C, P, N]

private def metricCompletionFunctorToEventFlow : MetricCompletionFunctorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionFunctorFields x).map metricCompletionFunctorEncodeBHist

private def metricCompletionFunctorEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionFunctorEventAt index rest

private def metricCompletionFunctorFromEventFlow (ef : EventFlow) :
    Option MetricCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionFunctorUp.mk
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 0 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 1 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 2 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 3 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 4 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 5 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 6 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 7 ef))
      (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEventAt 8 ef)))

private theorem MetricCompletionFunctorTasteGate_single_carrier_alignment_round_trip
    (x : MetricCompletionFunctorUp) :
    metricCompletionFunctorFromEventFlow (metricCompletionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M0 M1 G E T H C P N =>
      change
        some
          (MetricCompletionFunctorUp.mk
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist M0))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist M1))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist G))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist E))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist T))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist H))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist C))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist P))
            (metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist N))) =
          some (MetricCompletionFunctorUp.mk M0 M1 G E T H C P N)
      rw [MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode M0,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode M1,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode G,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode E,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode T,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionFunctorUp} :
    metricCompletionFunctorToEventFlow x = metricCompletionFunctorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionFunctorFromEventFlow (metricCompletionFunctorToEventFlow x) =
        metricCompletionFunctorFromEventFlow (metricCompletionFunctorToEventFlow y) :=
    congrArg metricCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionFunctorBHistCarrier : BHistCarrier MetricCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionFunctorToEventFlow
  fromEventFlow := metricCompletionFunctorFromEventFlow

instance metricCompletionFunctorChapterTasteGate :
    ChapterTasteGate MetricCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionFunctorFromEventFlow (metricCompletionFunctorToEventFlow x) = some x
    exact MetricCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricCompletionFunctorTasteGate_single_carrier_alignment :
    (forall h : BHist,
        metricCompletionFunctorDecodeBHist (metricCompletionFunctorEncodeBHist h) = h) ∧
      (forall x : MetricCompletionFunctorUp,
        metricCompletionFunctorFromEventFlow (metricCompletionFunctorToEventFlow x) = some x) ∧
        (forall x y : MetricCompletionFunctorUp,
          metricCompletionFunctorToEventFlow x = metricCompletionFunctorToEventFlow y -> x = y) ∧
          metricCompletionFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetricCompletionFunctorTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MetricCompletionFunctorTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MetricCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.MetricCompletionFunctorUp
