import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionMonadUp : Type where
  | mk (X Q U F V S H C P N : BHist) : MetricCompletionMonadUp
  deriving DecidableEq

def metricCompletionMonadEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionMonadEncodeBHist h

def metricCompletionMonadDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionMonadDecodeBHist tail)

private theorem MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionMonadFields : MetricCompletionMonadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionMonadUp.mk X Q U F V S H C P N => [X, Q, U, F, V, S, H, C, P, N]

def metricCompletionMonadToEventFlow : MetricCompletionMonadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionMonadFields x).map metricCompletionMonadEncodeBHist

private def metricCompletionMonadEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionMonadEventAtDefault index rest

def metricCompletionMonadFromEventFlow (ef : EventFlow) : Option MetricCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionMonadUp.mk
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 0 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 1 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 2 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 3 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 4 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 5 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 6 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 7 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 8 ef))
      (metricCompletionMonadDecodeBHist (metricCompletionMonadEventAtDefault 9 ef)))

private theorem MetricCompletionMonadTasteGate_single_carrier_alignment_round_trip
    (x : MetricCompletionMonadUp) :
    metricCompletionMonadFromEventFlow (metricCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Q U F V S H C P N =>
      change
        some
          (MetricCompletionMonadUp.mk
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist X))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist Q))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist U))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist F))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist V))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist S))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist H))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist C))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist P))
            (metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist N))) =
          some (MetricCompletionMonadUp.mk X Q U F V S H C P N)
      rw [MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode X,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode Q,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode U,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode F,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode V,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode S,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionMonadTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionMonadUp} :
    metricCompletionMonadToEventFlow x = metricCompletionMonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionMonadFromEventFlow (metricCompletionMonadToEventFlow x) =
        metricCompletionMonadFromEventFlow (metricCompletionMonadToEventFlow y) :=
    congrArg metricCompletionMonadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionMonadTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricCompletionMonadTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCompletionMonadTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetricCompletionMonadUp, metricCompletionMonadFields x = metricCompletionMonadFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Q₁ U₁ F₁ V₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Q₂ U₂ F₂ V₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metricCompletionMonadBHistCarrier : BHistCarrier MetricCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionMonadToEventFlow
  fromEventFlow := metricCompletionMonadFromEventFlow

instance metricCompletionMonadChapterTasteGate : ChapterTasteGate MetricCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionMonadFromEventFlow (metricCompletionMonadToEventFlow x) = some x
    exact MetricCompletionMonadTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCompletionMonadTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricCompletionMonadFieldFaithful : FieldFaithful MetricCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionMonadFields
  field_faithful := MetricCompletionMonadTasteGate_single_carrier_alignment_fields_faithful

def metricCompletionMonadTasteGate : ChapterTasteGate MetricCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionMonadChapterTasteGate

theorem MetricCompletionMonadTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricCompletionMonadDecodeBHist (metricCompletionMonadEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionMonadUp,
        metricCompletionMonadFromEventFlow (metricCompletionMonadToEventFlow x) = some x) ∧
        (∀ x y : MetricCompletionMonadUp,
          metricCompletionMonadToEventFlow x = metricCompletionMonadToEventFlow y → x = y) ∧
          metricCompletionMonadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨MetricCompletionMonadTasteGate_single_carrier_alignment_decode_encode,
      MetricCompletionMonadTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetricCompletionMonadTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionMonadUp
