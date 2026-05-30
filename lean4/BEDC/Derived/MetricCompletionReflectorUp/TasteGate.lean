import BEDC.Derived.MetricCompletionReflectorUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def metricCompletionReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionReflectorEncodeBHist h

def metricCompletionReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionReflectorDecodeBHist tail)

private theorem MetricCompletionReflectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionReflectorFields : MetricCompletionReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionReflectorUp.mk metricCompletion uniformCompletion separatedMetric
      cauchyReflector realSealHandoff transport replay provenance name =>
      [metricCompletion, uniformCompletion, separatedMetric, cauchyReflector, realSealHandoff,
        transport, replay, provenance, name]

def metricCompletionReflectorToEventFlow : MetricCompletionReflectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metricCompletionReflectorFields x).map metricCompletionReflectorEncodeBHist

private def metricCompletionReflectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionReflectorEventAtDefault index rest

def metricCompletionReflectorFromEventFlow
    (ef : EventFlow) : Option MetricCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionReflectorUp.mk
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 0 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 1 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 2 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 3 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 4 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 5 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 6 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 7 ef))
      (metricCompletionReflectorDecodeBHist
        (metricCompletionReflectorEventAtDefault 8 ef)))

private theorem MetricCompletionReflectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionReflectorUp,
      metricCompletionReflectorFromEventFlow
        (metricCompletionReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk metricCompletion uniformCompletion separatedMetric cauchyReflector realSealHandoff
      transport replay provenance name =>
      change
        some
          (MetricCompletionReflectorUp.mk
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist metricCompletion))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist uniformCompletion))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist separatedMetric))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist cauchyReflector))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist realSealHandoff))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist transport))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist replay))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist provenance))
            (metricCompletionReflectorDecodeBHist
              (metricCompletionReflectorEncodeBHist name))) =
          some
            (MetricCompletionReflectorUp.mk metricCompletion uniformCompletion separatedMetric
              cauchyReflector realSealHandoff transport replay provenance name)
      rw [MetricCompletionReflectorTasteGate_single_carrier_alignment_decode metricCompletion,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode uniformCompletion,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode separatedMetric,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode cauchyReflector,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode realSealHandoff,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode transport,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode replay,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode provenance,
        MetricCompletionReflectorTasteGate_single_carrier_alignment_decode name]

private theorem MetricCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionReflectorUp} :
    metricCompletionReflectorToEventFlow x = metricCompletionReflectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionReflectorFromEventFlow (metricCompletionReflectorToEventFlow x) =
        metricCompletionReflectorFromEventFlow (metricCompletionReflectorToEventFlow y) :=
    congrArg metricCompletionReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionReflectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCompletionReflectorTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetricCompletionReflectorUp,
      metricCompletionReflectorFields x = metricCompletionReflectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricCompletion₁ uniformCompletion₁ separatedMetric₁ cauchyReflector₁
      realSealHandoff₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk metricCompletion₂ uniformCompletion₂ separatedMetric₂ cauchyReflector₂
          realSealHandoff₂ transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hMetricCompletion tail0
          injection tail0 with hUniformCompletion tail1
          injection tail1 with hSeparatedMetric tail2
          injection tail2 with hCauchyReflector tail3
          injection tail3 with hRealSealHandoff tail4
          injection tail4 with hTransport tail5
          injection tail5 with hReplay tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hName _
          subst hMetricCompletion
          subst hUniformCompletion
          subst hSeparatedMetric
          subst hCauchyReflector
          subst hRealSealHandoff
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance metricCompletionReflectorBHistCarrier :
    BHistCarrier MetricCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionReflectorToEventFlow
  fromEventFlow := metricCompletionReflectorFromEventFlow

instance metricCompletionReflectorChapterTasteGate :
    ChapterTasteGate MetricCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionReflectorFromEventFlow (metricCompletionReflectorToEventFlow x) =
        some x
    exact MetricCompletionReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricCompletionReflectorFieldFaithful :
    FieldFaithful MetricCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionReflectorFields
  field_faithful := MetricCompletionReflectorTasteGate_single_carrier_alignment_fields

instance metricCompletionReflectorNontrivial : Nontrivial MetricCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCompletionReflectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricCompletionReflectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionReflectorChapterTasteGate

theorem MetricCompletionReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricCompletionReflectorDecodeBHist (metricCompletionReflectorEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionReflectorUp,
        metricCompletionReflectorFromEventFlow
          (metricCompletionReflectorToEventFlow x) = some x) ∧
        (∀ x y : MetricCompletionReflectorUp,
          metricCompletionReflectorToEventFlow x =
            metricCompletionReflectorToEventFlow y → x = y) ∧
          metricCompletionReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MetricCompletionReflectorTasteGate_single_carrier_alignment_decode,
      MetricCompletionReflectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetricCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionReflectorUp
