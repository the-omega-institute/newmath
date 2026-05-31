import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricIdentificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricIdentificationUp : Type where
  | mk (P M Z S C T R H K Q N : BHist) : MetricIdentificationUp
  deriving DecidableEq

def metricIdentificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricIdentificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricIdentificationEncodeBHist h

def metricIdentificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricIdentificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricIdentificationDecodeBHist tail)

private theorem MetricIdentificationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, metricIdentificationDecodeBHist (metricIdentificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricIdentificationFields : MetricIdentificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricIdentificationUp.mk P M Z S C T R H K Q N => [P, M, Z, S, C, T, R, H, K, Q, N]

def metricIdentificationToEventFlow : MetricIdentificationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricIdentificationFields x).map metricIdentificationEncodeBHist

private def metricIdentificationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricIdentificationEventAt index rest

def metricIdentificationFromEventFlow (ef : EventFlow) :
    Option MetricIdentificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricIdentificationUp.mk
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 0 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 1 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 2 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 3 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 4 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 5 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 6 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 7 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 8 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 9 ef))
      (metricIdentificationDecodeBHist (metricIdentificationEventAt 10 ef)))

private theorem MetricIdentificationTasteGate_single_carrier_alignment_round_trip
    (x : MetricIdentificationUp) :
    metricIdentificationFromEventFlow (metricIdentificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P M Z S C T R H K Q N =>
      change
        some
          (MetricIdentificationUp.mk
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist P))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist M))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist Z))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist S))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist C))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist T))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist R))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist H))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist K))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist Q))
            (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist N))) =
          some (MetricIdentificationUp.mk P M Z S C T R H K Q N)
      rw [MetricIdentificationTasteGate_single_carrier_alignment_decode_encode P,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode M,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode Z,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode S,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode C,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode T,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode R,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode H,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode K,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode Q,
        MetricIdentificationTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricIdentificationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricIdentificationUp} :
    metricIdentificationToEventFlow x = metricIdentificationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricIdentificationFromEventFlow (metricIdentificationToEventFlow x) =
        metricIdentificationFromEventFlow (metricIdentificationToEventFlow y) :=
    congrArg metricIdentificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricIdentificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricIdentificationTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricIdentificationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetricIdentificationUp, metricIdentificationFields x = metricIdentificationFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P₁ M₁ Z₁ S₁ C₁ T₁ R₁ H₁ K₁ Q₁ N₁ =>
      cases y with
      | mk P₂ M₂ Z₂ S₂ C₂ T₂ R₂ H₂ K₂ Q₂ N₂ =>
          cases hfields
          rfl

instance metricIdentificationBHistCarrier : BHistCarrier MetricIdentificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricIdentificationToEventFlow
  fromEventFlow := metricIdentificationFromEventFlow

instance metricIdentificationChapterTasteGate : ChapterTasteGate MetricIdentificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricIdentificationFromEventFlow (metricIdentificationToEventFlow x) = some x
    exact MetricIdentificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricIdentificationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricIdentificationFieldFaithful : FieldFaithful MetricIdentificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricIdentificationFields
  field_faithful := MetricIdentificationTasteGate_single_carrier_alignment_fields_faithful

instance metricIdentificationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetricIdentificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricIdentificationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricIdentificationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def metricIdentificationTasteGate : ChapterTasteGate MetricIdentificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricIdentificationChapterTasteGate

theorem MetricIdentificationTasteGate_single_carrier_alignment :
    (metricIdentificationDecodeBHist (metricIdentificationEncodeBHist BHist.Empty) =
        BHist.Empty) ∧
      (metricIdentificationEncodeBHist (BHist.e0 BHist.Empty) = BMark.b0 :: []) ∧
        Nonempty (BHistCarrier MetricIdentificationUp) ∧
          Nonempty (ChapterTasteGate MetricIdentificationUp) ∧
            (∀ x : MetricIdentificationUp,
              metricIdentificationFromEventFlow (metricIdentificationToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl, ⟨metricIdentificationBHistCarrier⟩,
      ⟨metricIdentificationChapterTasteGate⟩,
      MetricIdentificationTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.MetricIdentificationUp
