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

def metricTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricTopologyEncodeBHist h

def metricTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricTopologyDecodeBHist tail)

private theorem metricTopology_decode_encode_bhist :
    ∀ h : BHist, metricTopologyDecodeBHist (metricTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricTopologyFields : MetricTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricTopologyUp.mk M B T R Q H C P N => [M, B, T, R, Q, H, C, P, N]

def metricTopologyToEventFlow : MetricTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricTopologyFields x).map metricTopologyEncodeBHist

private def metricTopologyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricTopologyEventAtDefault index rest

def metricTopologyFromEventFlow (ef : EventFlow) : Option MetricTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricTopologyUp.mk
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 0 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 1 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 2 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 3 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 4 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 5 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 6 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 7 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 8 ef)))

private theorem metricTopology_round_trip :
    ∀ x : MetricTopologyUp,
      metricTopologyFromEventFlow (metricTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B T R Q H C P N =>
      change
        some
          (MetricTopologyUp.mk
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist M))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist B))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist T))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist R))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist Q))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist H))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist C))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist P))
            (metricTopologyDecodeBHist (metricTopologyEncodeBHist N))) =
          some (MetricTopologyUp.mk M B T R Q H C P N)
      rw [metricTopology_decode_encode_bhist M,
        metricTopology_decode_encode_bhist B,
        metricTopology_decode_encode_bhist T,
        metricTopology_decode_encode_bhist R,
        metricTopology_decode_encode_bhist Q,
        metricTopology_decode_encode_bhist H,
        metricTopology_decode_encode_bhist C,
        metricTopology_decode_encode_bhist P,
        metricTopology_decode_encode_bhist N]

private theorem metricTopologyToEventFlow_injective {x y : MetricTopologyUp} :
    metricTopologyToEventFlow x = metricTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricTopologyFromEventFlow (metricTopologyToEventFlow x) =
        metricTopologyFromEventFlow (metricTopologyToEventFlow y) :=
    congrArg metricTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricTopology_round_trip x).symm
      (Eq.trans hread (metricTopology_round_trip y)))

private theorem metricTopology_fields_faithful :
    ∀ x y : MetricTopologyUp, metricTopologyFields x = metricTopologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 B1 T1 R1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 B2 T2 R2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricTopologyBHistCarrier : BHistCarrier MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricTopologyToEventFlow
  fromEventFlow := metricTopologyFromEventFlow

instance metricTopologyChapterTasteGate : ChapterTasteGate MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricTopologyFromEventFlow (metricTopologyToEventFlow x) = some x
    exact metricTopology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricTopologyToEventFlow_injective heq)

instance metricTopologyFieldFaithful : FieldFaithful MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricTopologyFields
  field_faithful := metricTopology_fields_faithful

instance metricTopologyNontrivial : Nontrivial MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricTopologyChapterTasteGate

theorem MetricTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricTopologyDecodeBHist (metricTopologyEncodeBHist h) = h) ∧
      (∀ x : MetricTopologyUp,
        metricTopologyFromEventFlow (metricTopologyToEventFlow x) = some x) ∧
        (∀ x y : MetricTopologyUp,
          metricTopologyToEventFlow x = metricTopologyToEventFlow y → x = y) ∧
          metricTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨metricTopology_decode_encode_bhist,
      metricTopology_round_trip,
      (fun _ _ heq => metricTopologyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricTopologyUp.TasteGate
