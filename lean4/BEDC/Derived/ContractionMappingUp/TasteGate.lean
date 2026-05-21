import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractionMappingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractionMappingUp : Type where
  | mk
      (metricCarrier metricDistance selfMap graph contractionBound modulusRow picardRoute
        transportRows continuationRows provenance nameCert : BHist) :
      ContractionMappingUp
  deriving DecidableEq

def contractionMappingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractionMappingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractionMappingEncodeBHist h

def contractionMappingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractionMappingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractionMappingDecodeBHist tail)

private theorem ContractionMappingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractionMappingFields : ContractionMappingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractionMappingUp.mk metricCarrier metricDistance selfMap graph contractionBound
      modulusRow picardRoute transportRows continuationRows provenance nameCert =>
      [metricCarrier, metricDistance, selfMap, graph, contractionBound, modulusRow,
        picardRoute, transportRows, continuationRows, provenance, nameCert]

def contractionMappingToEventFlow : ContractionMappingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractionMappingFields x).map contractionMappingEncodeBHist

private def contractionMappingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contractionMappingEventAtDefault index rest

def contractionMappingFromEventFlow : EventFlow → Option ContractionMappingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ContractionMappingUp.mk
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 0 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 1 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 2 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 3 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 4 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 5 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 6 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 7 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 8 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 9 ef))
        (contractionMappingDecodeBHist (contractionMappingEventAtDefault 10 ef)))

private theorem ContractionMappingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContractionMappingUp,
      contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricCarrier metricDistance selfMap graph contractionBound modulusRow picardRoute
      transportRows continuationRows provenance nameCert =>
      change
        some
          (ContractionMappingUp.mk
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist metricCarrier))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist metricDistance))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist selfMap))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist graph))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist contractionBound))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist modulusRow))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist picardRoute))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist transportRows))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist continuationRows))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist provenance))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist nameCert))) =
          some
            (ContractionMappingUp.mk metricCarrier metricDistance selfMap graph
              contractionBound modulusRow picardRoute transportRows continuationRows provenance
              nameCert)
      rw [ContractionMappingTasteGate_single_carrier_alignment_decode metricCarrier,
        ContractionMappingTasteGate_single_carrier_alignment_decode metricDistance,
        ContractionMappingTasteGate_single_carrier_alignment_decode selfMap,
        ContractionMappingTasteGate_single_carrier_alignment_decode graph,
        ContractionMappingTasteGate_single_carrier_alignment_decode contractionBound,
        ContractionMappingTasteGate_single_carrier_alignment_decode modulusRow,
        ContractionMappingTasteGate_single_carrier_alignment_decode picardRoute,
        ContractionMappingTasteGate_single_carrier_alignment_decode transportRows,
        ContractionMappingTasteGate_single_carrier_alignment_decode continuationRows,
        ContractionMappingTasteGate_single_carrier_alignment_decode provenance,
        ContractionMappingTasteGate_single_carrier_alignment_decode nameCert]

private theorem contractionMappingToEventFlow_injective {x y : ContractionMappingUp} :
    contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractionMappingFromEventFlow (contractionMappingToEventFlow x) =
        contractionMappingFromEventFlow (contractionMappingToEventFlow y) :=
    congrArg contractionMappingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContractionMappingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContractionMappingTasteGate_single_carrier_alignment_round_trip y)))

private theorem contractionMapping_field_faithful :
    ∀ x y : ContractionMappingUp,
      contractionMappingFields x = contractionMappingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricCarrier₁ metricDistance₁ selfMap₁ graph₁ contractionBound₁ modulusRow₁
      picardRoute₁ transportRows₁ continuationRows₁ provenance₁ nameCert₁ =>
      cases y with
      | mk metricCarrier₂ metricDistance₂ selfMap₂ graph₂ contractionBound₂ modulusRow₂
          picardRoute₂ transportRows₂ continuationRows₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance contractionMappingBHistCarrier : BHistCarrier ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractionMappingToEventFlow
  fromEventFlow := contractionMappingFromEventFlow

instance contractionMappingChapterTasteGate : ChapterTasteGate ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x
    exact ContractionMappingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contractionMappingToEventFlow_injective heq)

instance contractionMappingFieldFaithful : FieldFaithful ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contractionMappingFields
  field_faithful := contractionMapping_field_faithful

def taste_gate : ChapterTasteGate ContractionMappingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contractionMappingChapterTasteGate

theorem ContractionMappingTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ContractionMappingUp) ∧
      Nonempty (ChapterTasteGate ContractionMappingUp) ∧
      Nonempty (FieldFaithful ContractionMappingUp) ∧
      (∀ h : BHist, contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h) ∧
      (∀ x : ContractionMappingUp,
        contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x) ∧
      (∀ x y : ContractionMappingUp,
        contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y) ∧
      contractionMappingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨contractionMappingBHistCarrier⟩
  constructor
  · exact ⟨contractionMappingChapterTasteGate⟩
  constructor
  · exact ⟨contractionMappingFieldFaithful⟩
  constructor
  · exact ContractionMappingTasteGate_single_carrier_alignment_decode
  constructor
  · exact ContractionMappingTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact contractionMappingToEventFlow_injective heq
  · rfl

namespace TasteGate

theorem ContractionMappingTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ContractionMappingUp) ∧
      Nonempty (ChapterTasteGate ContractionMappingUp) ∧
      Nonempty (FieldFaithful ContractionMappingUp) ∧
      (∀ h : BHist, contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h) ∧
      (∀ x : ContractionMappingUp,
        contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x) ∧
      (∀ x y : ContractionMappingUp,
        contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y) ∧
      contractionMappingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  exact BEDC.Derived.ContractionMappingUp.ContractionMappingTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.ContractionMappingUp
