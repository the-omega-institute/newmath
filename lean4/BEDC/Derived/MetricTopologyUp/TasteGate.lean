import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricTopologyUp

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

private theorem MetricTopologyTasteGate_single_carrier_alignment_decode :
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
  | x => [BMark.b0, BMark.b1, BMark.b0, BMark.b1] ::
      (metricTopologyFields x).map metricTopologyEncodeBHist

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
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 1 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 2 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 3 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 4 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 5 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 6 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 7 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 8 ef))
      (metricTopologyDecodeBHist (metricTopologyEventAtDefault 9 ef)))

private theorem MetricTopologyTasteGate_single_carrier_alignment_round_trip :
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
      rw [MetricTopologyTasteGate_single_carrier_alignment_decode M,
        MetricTopologyTasteGate_single_carrier_alignment_decode B,
        MetricTopologyTasteGate_single_carrier_alignment_decode T,
        MetricTopologyTasteGate_single_carrier_alignment_decode R,
        MetricTopologyTasteGate_single_carrier_alignment_decode Q,
        MetricTopologyTasteGate_single_carrier_alignment_decode H,
        MetricTopologyTasteGate_single_carrier_alignment_decode C,
        MetricTopologyTasteGate_single_carrier_alignment_decode P,
        MetricTopologyTasteGate_single_carrier_alignment_decode N]

private theorem MetricTopologyTasteGate_single_carrier_alignment_injective
    {x y : MetricTopologyUp} :
    metricTopologyToEventFlow x = metricTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricTopologyFromEventFlow (metricTopologyToEventFlow x) =
        metricTopologyFromEventFlow (metricTopologyToEventFlow y) :=
    congrArg metricTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricTopologyTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricTopologyTasteGate_single_carrier_alignment_fields :
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
    exact MetricTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricTopologyTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate MetricTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricTopologyChapterTasteGate

instance metricTopologyFieldFaithful : FieldFaithful MetricTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricTopologyFields
  field_faithful := MetricTopologyTasteGate_single_carrier_alignment_fields

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

theorem MetricTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricTopologyDecodeBHist (metricTopologyEncodeBHist h) = h) ∧
      (∀ x : MetricTopologyUp,
        metricTopologyFromEventFlow (metricTopologyToEventFlow x) = some x) ∧
        (∀ x y : MetricTopologyUp,
          metricTopologyToEventFlow x = metricTopologyToEventFlow y → x = y) ∧
          metricTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MetricTopologyTasteGate_single_carrier_alignment_decode,
      MetricTopologyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MetricTopologyTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.MetricTopologyUp
