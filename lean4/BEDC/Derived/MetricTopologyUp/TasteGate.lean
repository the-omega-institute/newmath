import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricTopologyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricTopologyUp : Type where
  | mk (M B T R Q H C P N : BHist) : MetricTopologyUp
  deriving DecidableEq

def MetricTopologyTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      MetricTopologyTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      MetricTopologyTasteGate_single_carrier_alignment_encodeBHist h

def MetricTopologyTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem MetricTopologyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
        (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def MetricTopologyTasteGate_single_carrier_alignment_fields :
    MetricTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricTopologyUp.mk M B T R Q H C P N => [M, B, T, R, Q, H, C, P, N]

def MetricTopologyTasteGate_single_carrier_alignment_toEventFlow :
    MetricTopologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (MetricTopologyTasteGate_single_carrier_alignment_fields x).map
      MetricTopologyTasteGate_single_carrier_alignment_encodeBHist

private def MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault index rest

def MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MetricTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricTopologyUp.mk
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
          (MetricTopologyTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

private theorem MetricTopologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricTopologyUp,
      MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow
        (MetricTopologyTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B T R Q H C P N =>
      change
        some
          (MetricTopologyUp.mk
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist M))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist B))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist T))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist R))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist Q))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist H))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist C))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist P))
            (MetricTopologyTasteGate_single_carrier_alignment_decodeBHist
              (MetricTopologyTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (MetricTopologyUp.mk M B T R Q H C P N)
      rw [MetricTopologyTasteGate_single_carrier_alignment_decode M,
        MetricTopologyTasteGate_single_carrier_alignment_decode B,
        MetricTopologyTasteGate_single_carrier_alignment_decode T,
        MetricTopologyTasteGate_single_carrier_alignment_decode R,
        MetricTopologyTasteGate_single_carrier_alignment_decode Q,
        MetricTopologyTasteGate_single_carrier_alignment_decode H,
        MetricTopologyTasteGate_single_carrier_alignment_decode C,
        MetricTopologyTasteGate_single_carrier_alignment_decode P,
        MetricTopologyTasteGate_single_carrier_alignment_decode N]

private theorem MetricTopologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricTopologyUp} :
    MetricTopologyTasteGate_single_carrier_alignment_toEventFlow x =
      MetricTopologyTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow
          (MetricTopologyTasteGate_single_carrier_alignment_toEventFlow x) =
        MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow
          (MetricTopologyTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricTopologyTasteGate_single_carrier_alignment_round_trip y)))

instance metricTopologyBHistCarrier : BHistCarrier MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MetricTopologyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow

instance metricTopologyChapterTasteGate :
    ChapterTasteGate MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MetricTopologyTasteGate_single_carrier_alignment_fromEventFlow
        (MetricTopologyTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact MetricTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricTopologyTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier MetricTopologyUp) ∧
      Nonempty (ChapterTasteGate MetricTopologyUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨metricTopologyBHistCarrier⟩, ⟨metricTopologyChapterTasteGate⟩⟩

end BEDC.Derived.MetricTopologyUp.TasteGate
