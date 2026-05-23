import BEDC.Derived.CompactMetricUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricUp : Type where
  | mk
      (metricCarrier metricClassifier metricDistance finiteNetSelector limitWitness : BHist) :
      CompactMetricUp
  deriving DecidableEq

def compactMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricEncodeBHist h

def compactMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricDecodeBHist tail)

private theorem compactMetric_decode_encode_bhist :
    ∀ h : BHist, compactMetricDecodeBHist (compactMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricFields : CompactMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricUp.mk metricCarrier metricClassifier metricDistance finiteNetSelector
      limitWitness =>
      [metricCarrier, metricClassifier, metricDistance, finiteNetSelector, limitWitness]

def compactMetricToEventFlow : CompactMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactMetricFields x).map compactMetricEncodeBHist

private def compactMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactMetricEventAtDefault index rest

def compactMetricFromEventFlow : EventFlow → Option CompactMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactMetricUp.mk
        (compactMetricDecodeBHist (compactMetricEventAtDefault 0 ef))
        (compactMetricDecodeBHist (compactMetricEventAtDefault 1 ef))
        (compactMetricDecodeBHist (compactMetricEventAtDefault 2 ef))
        (compactMetricDecodeBHist (compactMetricEventAtDefault 3 ef))
        (compactMetricDecodeBHist (compactMetricEventAtDefault 4 ef)))

private theorem compactMetric_round_trip :
    ∀ x : CompactMetricUp,
      compactMetricFromEventFlow (compactMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricCarrier metricClassifier metricDistance finiteNetSelector limitWitness =>
      change
        some
          (CompactMetricUp.mk
            (compactMetricDecodeBHist (compactMetricEncodeBHist metricCarrier))
            (compactMetricDecodeBHist (compactMetricEncodeBHist metricClassifier))
            (compactMetricDecodeBHist (compactMetricEncodeBHist metricDistance))
            (compactMetricDecodeBHist (compactMetricEncodeBHist finiteNetSelector))
            (compactMetricDecodeBHist (compactMetricEncodeBHist limitWitness))) =
          some
            (CompactMetricUp.mk metricCarrier metricClassifier metricDistance
              finiteNetSelector limitWitness)
      rw [compactMetric_decode_encode_bhist metricCarrier,
        compactMetric_decode_encode_bhist metricClassifier,
        compactMetric_decode_encode_bhist metricDistance,
        compactMetric_decode_encode_bhist finiteNetSelector,
        compactMetric_decode_encode_bhist limitWitness]

private theorem compactMetricToEventFlow_injective {x y : CompactMetricUp} :
    compactMetricToEventFlow x = compactMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricFromEventFlow (compactMetricToEventFlow x) =
        compactMetricFromEventFlow (compactMetricToEventFlow y) :=
    congrArg compactMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactMetric_round_trip x).symm
      (Eq.trans hread (compactMetric_round_trip y)))

private theorem compactMetric_field_faithful :
    ∀ x y : CompactMetricUp, compactMetricFields x = compactMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricCarrier₁ metricClassifier₁ metricDistance₁ finiteNetSelector₁ limitWitness₁ =>
      cases y with
      | mk metricCarrier₂ metricClassifier₂ metricDistance₂ finiteNetSelector₂ limitWitness₂ =>
          cases hfields
          rfl

instance compactMetricBHistCarrier : BHistCarrier CompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricToEventFlow
  fromEventFlow := compactMetricFromEventFlow

instance compactMetricChapterTasteGate : ChapterTasteGate CompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactMetricFromEventFlow (compactMetricToEventFlow x) = some x
    exact compactMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactMetricToEventFlow_injective heq)

instance compactMetricFieldFaithful : FieldFaithful CompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactMetricFields
  field_faithful := compactMetric_field_faithful

def taste_gate : ChapterTasteGate CompactMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactMetricChapterTasteGate

theorem CompactMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactMetricDecodeBHist (compactMetricEncodeBHist h) = h) ∧
      (∀ x : CompactMetricUp,
        compactMetricFromEventFlow (compactMetricToEventFlow x) = some x) ∧
        (∀ x y : CompactMetricUp,
          compactMetricToEventFlow x = compactMetricToEventFlow y → x = y) ∧
          compactMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨compactMetric_decode_encode_bhist,
      compactMetric_round_trip,
      (fun _ _ heq => compactMetricToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactMetricUp
