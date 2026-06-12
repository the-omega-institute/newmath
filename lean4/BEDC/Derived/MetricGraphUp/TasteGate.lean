import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricGraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricGraphUp : Type where
  | mk (G E W S L D B T H C P N : BHist) : MetricGraphUp
  deriving DecidableEq

def metricGraphEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricGraphEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricGraphEncodeBHist h

def metricGraphDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricGraphDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricGraphDecodeBHist tail)

private theorem metricGraphDecode_encode_bhist :
    ∀ h : BHist, metricGraphDecodeBHist (metricGraphEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricGraphFields : MetricGraphUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricGraphUp.mk G E W S L D B T H C P N => [G, E, W, S, L, D, B, T, H, C, P, N]

def metricGraphToEventFlow : MetricGraphUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricGraphFields x).map metricGraphEncodeBHist

private def metricGraphEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricGraphEventAtDefault index rest

def metricGraphFromEventFlow (ef : EventFlow) : Option MetricGraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricGraphUp.mk
      (metricGraphDecodeBHist (metricGraphEventAtDefault 0 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 1 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 2 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 3 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 4 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 5 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 6 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 7 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 8 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 9 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 10 ef))
      (metricGraphDecodeBHist (metricGraphEventAtDefault 11 ef)))

private theorem MetricGraphTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricGraphUp,
      metricGraphFromEventFlow (metricGraphToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G E W S L D B T H C P N =>
      change
        some
          (MetricGraphUp.mk
            (metricGraphDecodeBHist (metricGraphEncodeBHist G))
            (metricGraphDecodeBHist (metricGraphEncodeBHist E))
            (metricGraphDecodeBHist (metricGraphEncodeBHist W))
            (metricGraphDecodeBHist (metricGraphEncodeBHist S))
            (metricGraphDecodeBHist (metricGraphEncodeBHist L))
            (metricGraphDecodeBHist (metricGraphEncodeBHist D))
            (metricGraphDecodeBHist (metricGraphEncodeBHist B))
            (metricGraphDecodeBHist (metricGraphEncodeBHist T))
            (metricGraphDecodeBHist (metricGraphEncodeBHist H))
            (metricGraphDecodeBHist (metricGraphEncodeBHist C))
            (metricGraphDecodeBHist (metricGraphEncodeBHist P))
            (metricGraphDecodeBHist (metricGraphEncodeBHist N))) =
          some (MetricGraphUp.mk G E W S L D B T H C P N)
      rw [metricGraphDecode_encode_bhist G, metricGraphDecode_encode_bhist E,
        metricGraphDecode_encode_bhist W, metricGraphDecode_encode_bhist S,
        metricGraphDecode_encode_bhist L, metricGraphDecode_encode_bhist D,
        metricGraphDecode_encode_bhist B, metricGraphDecode_encode_bhist T,
        metricGraphDecode_encode_bhist H, metricGraphDecode_encode_bhist C,
        metricGraphDecode_encode_bhist P, metricGraphDecode_encode_bhist N]

private theorem MetricGraphTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricGraphUp} :
    metricGraphToEventFlow x = metricGraphToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricGraphFromEventFlow (metricGraphToEventFlow x) =
        metricGraphFromEventFlow (metricGraphToEventFlow y) :=
    congrArg metricGraphFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricGraphTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricGraphTasteGate_single_carrier_alignment_round_trip y)))

instance metricGraphBHistCarrier : BHistCarrier MetricGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricGraphToEventFlow
  fromEventFlow := metricGraphFromEventFlow

instance metricGraphChapterTasteGate : ChapterTasteGate MetricGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricGraphFromEventFlow (metricGraphToEventFlow x) = some x
    exact MetricGraphTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricGraphTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricGraphTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricGraphDecodeBHist (metricGraphEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricGraphUp) ∧
        Nonempty (ChapterTasteGate MetricGraphUp) ∧
          metricGraphEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨metricGraphDecode_encode_bhist, ⟨metricGraphBHistCarrier⟩,
      ⟨metricGraphChapterTasteGate⟩, rfl⟩

end BEDC.Derived.MetricGraphUp
