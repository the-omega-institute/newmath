import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionUp : Type where
  | mk (M C S D R E H P N : BHist) : MetricCompletionUp
  deriving DecidableEq

def metricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionEncodeBHist h

def metricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionDecodeBHist tail)

private theorem MetricCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, metricCompletionDecodeBHist (metricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionFields : MetricCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionUp.mk M C S D R E H P N => [M, C, S, D, R, E, H, P, N]

def metricCompletionToEventFlow : MetricCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionFields x).map metricCompletionEncodeBHist

private def MetricCompletionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MetricCompletionTasteGate_single_carrier_alignment_eventAt index rest

def metricCompletionFromEventFlow (ef : EventFlow) : Option MetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionUp.mk
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (metricCompletionDecodeBHist
        (MetricCompletionTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem MetricCompletionTasteGate_single_carrier_alignment_round_trip
    (x : MetricCompletionUp) :
    metricCompletionFromEventFlow (metricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M C S D R E H P N =>
      change
        some
          (MetricCompletionUp.mk
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist M))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist C))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist S))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist D))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist R))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist E))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist H))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist P))
            (metricCompletionDecodeBHist (metricCompletionEncodeBHist N))) =
          some (MetricCompletionUp.mk M C S D R E H P N)
      rw [MetricCompletionTasteGate_single_carrier_alignment_decode_encode M,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode S,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode D,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode E,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionUp} :
    metricCompletionToEventFlow x = metricCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionFromEventFlow (metricCompletionToEventFlow x) =
        metricCompletionFromEventFlow (metricCompletionToEventFlow y) :=
    congrArg metricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetricCompletionUp, metricCompletionFields x = metricCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ C₁ S₁ D₁ R₁ E₁ H₁ P₁ N₁ =>
      cases y with
      | mk M₂ C₂ S₂ D₂ R₂ E₂ H₂ P₂ N₂ =>
          cases hfields
          rfl

instance metricCompletionBHistCarrier : BHistCarrier MetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionToEventFlow
  fromEventFlow := metricCompletionFromEventFlow

instance metricCompletionChapterTasteGate : ChapterTasteGate MetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionFromEventFlow (metricCompletionToEventFlow x) = some x
    exact MetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricCompletionFieldFaithful : FieldFaithful MetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionFields
  field_faithful := MetricCompletionTasteGate_single_carrier_alignment_fields_faithful

instance metricCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def metricCompletionTasteGate : ChapterTasteGate MetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionChapterTasteGate

theorem MetricCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricCompletionUp) ∧
      Nonempty (FieldFaithful MetricCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetricCompletionUp) ∧
          (∀ h : BHist, metricCompletionDecodeBHist (metricCompletionEncodeBHist h) = h) ∧
            (∀ x : MetricCompletionUp,
              metricCompletionFromEventFlow (metricCompletionToEventFlow x) = some x) ∧
              (∀ x y : MetricCompletionUp,
                metricCompletionToEventFlow x = metricCompletionToEventFlow y → x = y) ∧
                metricCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨metricCompletionChapterTasteGate⟩,
      ⟨metricCompletionFieldFaithful⟩,
      ⟨metricCompletionNontrivial⟩,
      MetricCompletionTasteGate_single_carrier_alignment_decode_encode,
      MetricCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionUp.TasteGate
