import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricBaireSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricBaireSpaceUp : Type where
  | mk (M K D S R B H C P0 N : BHist) : MetricBaireSpaceUp
  deriving DecidableEq

def metricBaireSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricBaireSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricBaireSpaceEncodeBHist h

def metricBaireSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricBaireSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricBaireSpaceDecodeBHist tail)

private theorem MetricBaireSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricBaireSpaceFields : MetricBaireSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricBaireSpaceUp.mk M K D S R B H C P0 N => [M, K, D, S, R, B, H, C, P0, N]

def metricBaireSpaceToEventFlow : MetricBaireSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metricBaireSpaceFields x).map metricBaireSpaceEncodeBHist

private def metricBaireSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricBaireSpaceEventAtDefault index rest

def metricBaireSpaceFromEventFlow (ef : EventFlow) : Option MetricBaireSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricBaireSpaceUp.mk
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 0 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 1 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 2 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 3 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 4 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 5 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 6 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 7 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 8 ef))
      (metricBaireSpaceDecodeBHist (metricBaireSpaceEventAtDefault 9 ef)))

private theorem MetricBaireSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricBaireSpaceUp,
      metricBaireSpaceFromEventFlow (metricBaireSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K D S R B H C P0 N =>
      change
        some
          (MetricBaireSpaceUp.mk
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist M))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist K))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist D))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist S))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist R))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist B))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist H))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist C))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist P0))
            (metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist N))) =
          some (MetricBaireSpaceUp.mk M K D S R B H C P0 N)
      rw [MetricBaireSpaceTasteGate_single_carrier_alignment_decode M,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode K,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode D,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode S,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode R,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode B,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode H,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode C,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode P0,
        MetricBaireSpaceTasteGate_single_carrier_alignment_decode N]

private theorem MetricBaireSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricBaireSpaceUp} :
    metricBaireSpaceToEventFlow x = metricBaireSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricBaireSpaceFromEventFlow (metricBaireSpaceToEventFlow x) =
        metricBaireSpaceFromEventFlow (metricBaireSpaceToEventFlow y) :=
    congrArg metricBaireSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricBaireSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricBaireSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricBaireSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetricBaireSpaceUp, metricBaireSpaceFields x = metricBaireSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 K1 D1 S1 R1 B1 H1 C1 P01 N1 =>
      cases y with
      | mk M2 K2 D2 S2 R2 B2 H2 C2 P02 N2 =>
          cases hfields
          rfl

instance metricBaireSpaceBHistCarrier : BHistCarrier MetricBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricBaireSpaceToEventFlow
  fromEventFlow := metricBaireSpaceFromEventFlow

instance metricBaireSpaceChapterTasteGate : ChapterTasteGate MetricBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricBaireSpaceFromEventFlow (metricBaireSpaceToEventFlow x) = some x
    exact MetricBaireSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricBaireSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricBaireSpaceFieldFaithful : FieldFaithful MetricBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricBaireSpaceFields
  field_faithful := MetricBaireSpaceTasteGate_single_carrier_alignment_fields

instance metricBaireSpaceNontrivial : Nontrivial MetricBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricBaireSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricBaireSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricBaireSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricBaireSpaceChapterTasteGate

theorem MetricBaireSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricBaireSpaceDecodeBHist (metricBaireSpaceEncodeBHist h) = h) ∧
      metricBaireSpaceEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : MetricBaireSpaceUp, metricBaireSpaceFields x = metricBaireSpaceFields y →
          x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨MetricBaireSpaceTasteGate_single_carrier_alignment_decode, rfl,
      MetricBaireSpaceTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.MetricBaireSpaceUp
