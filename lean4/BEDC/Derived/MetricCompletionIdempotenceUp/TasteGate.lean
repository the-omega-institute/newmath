import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionIdempotenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionIdempotenceUp : Type where
  | mk (M S C U R H K P N : BHist) : MetricCompletionIdempotenceUp
  deriving DecidableEq

def metricCompletionIdempotenceEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionIdempotenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionIdempotenceEncodeBHist h

def metricCompletionIdempotenceDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionIdempotenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionIdempotenceDecodeBHist tail)

private theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionIdempotenceFields : MetricCompletionIdempotenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionIdempotenceUp.mk M S C U R H K P N => [M, S, C, U, R, H, K, P, N]

def metricCompletionIdempotenceToEventFlow : MetricCompletionIdempotenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionIdempotenceFields x).map metricCompletionIdempotenceEncodeBHist

private def metricCompletionIdempotenceEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionIdempotenceEventAtDefault index rest

def metricCompletionIdempotenceFromEventFlow (ef : EventFlow) :
    Option MetricCompletionIdempotenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionIdempotenceUp.mk
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 0 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 1 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 2 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 3 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 4 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 5 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 6 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 7 ef))
      (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEventAtDefault 8 ef)))

private theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip
    (x : MetricCompletionIdempotenceUp) :
    metricCompletionIdempotenceFromEventFlow (metricCompletionIdempotenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S C U R H K P N =>
      change
        some
          (MetricCompletionIdempotenceUp.mk
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist M))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist S))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist C))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist U))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist R))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist H))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist K))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist P))
            (metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist N))) =
          some (MetricCompletionIdempotenceUp.mk M S C U R H K P N)
      rw [MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode M,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode S,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode C,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode U,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode R,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode H,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode K,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode P,
        MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode N]

private theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionIdempotenceUp} :
    metricCompletionIdempotenceToEventFlow x = metricCompletionIdempotenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionIdempotenceFromEventFlow (metricCompletionIdempotenceToEventFlow x) =
        metricCompletionIdempotenceFromEventFlow (metricCompletionIdempotenceToEventFlow y) :=
    congrArg metricCompletionIdempotenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionIdempotenceBHistCarrier :
    BHistCarrier MetricCompletionIdempotenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionIdempotenceToEventFlow
  fromEventFlow := metricCompletionIdempotenceFromEventFlow

instance metricCompletionIdempotenceChapterTasteGate :
    ChapterTasteGate MetricCompletionIdempotenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionIdempotenceFromEventFlow (metricCompletionIdempotenceToEventFlow x) =
        some x
    exact MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionIdempotenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricCompletionIdempotenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metricCompletionIdempotenceDecodeBHist (metricCompletionIdempotenceEncodeBHist h) = h) ∧
      (forall x : MetricCompletionIdempotenceUp,
        metricCompletionIdempotenceFromEventFlow
          (metricCompletionIdempotenceToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier MetricCompletionIdempotenceUp) ∧
          Nonempty (ChapterTasteGate MetricCompletionIdempotenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact MetricCompletionIdempotenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact MetricCompletionIdempotenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · exact ⟨metricCompletionIdempotenceBHistCarrier⟩
  · exact ⟨metricCompletionIdempotenceChapterTasteGate⟩

end BEDC.Derived.MetricCompletionIdempotenceUp
