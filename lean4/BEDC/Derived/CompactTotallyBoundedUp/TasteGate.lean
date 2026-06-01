import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactTotallyBoundedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactTotallyBoundedUp : Type where
  | mk
      (metric completeMetric totallyBounded radiusSchedule exactness transport replay
        provenance localName : BHist) :
      CompactTotallyBoundedUp
  deriving DecidableEq

def compactTotallyBoundedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactTotallyBoundedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactTotallyBoundedEncodeBHist h

def compactTotallyBoundedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactTotallyBoundedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactTotallyBoundedDecodeBHist tail)

private theorem compactTotallyBounded_decode_encode_bhist :
    ∀ h : BHist, compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactTotallyBoundedFields : CompactTotallyBoundedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactTotallyBoundedUp.mk metric completeMetric totallyBounded radiusSchedule exactness
      transport replay provenance localName =>
      [metric, completeMetric, totallyBounded, radiusSchedule, exactness, transport, replay,
        provenance, localName]

def compactTotallyBoundedToEventFlow : CompactTotallyBoundedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactTotallyBoundedFields x).map compactTotallyBoundedEncodeBHist

private def compactTotallyBoundedEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactTotallyBoundedEventAtDefault index rest

def compactTotallyBoundedFromEventFlow : EventFlow → Option CompactTotallyBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactTotallyBoundedUp.mk
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 0 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 1 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 2 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 3 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 4 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 5 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 6 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 7 ef))
        (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEventAtDefault 8 ef)))

private theorem compactTotallyBounded_round_trip :
    ∀ x : CompactTotallyBoundedUp,
      compactTotallyBoundedFromEventFlow (compactTotallyBoundedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric completeMetric totallyBounded radiusSchedule exactness transport replay
      provenance localName =>
      change
        some
          (CompactTotallyBoundedUp.mk
            (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist metric))
            (compactTotallyBoundedDecodeBHist
              (compactTotallyBoundedEncodeBHist completeMetric))
            (compactTotallyBoundedDecodeBHist
              (compactTotallyBoundedEncodeBHist totallyBounded))
            (compactTotallyBoundedDecodeBHist
              (compactTotallyBoundedEncodeBHist radiusSchedule))
            (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist exactness))
            (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist transport))
            (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist replay))
            (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist provenance))
            (compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist localName))) =
          some
            (CompactTotallyBoundedUp.mk metric completeMetric totallyBounded radiusSchedule
              exactness transport replay provenance localName)
      rw [compactTotallyBounded_decode_encode_bhist metric,
        compactTotallyBounded_decode_encode_bhist completeMetric,
        compactTotallyBounded_decode_encode_bhist totallyBounded,
        compactTotallyBounded_decode_encode_bhist radiusSchedule,
        compactTotallyBounded_decode_encode_bhist exactness,
        compactTotallyBounded_decode_encode_bhist transport,
        compactTotallyBounded_decode_encode_bhist replay,
        compactTotallyBounded_decode_encode_bhist provenance,
        compactTotallyBounded_decode_encode_bhist localName]

private theorem compactTotallyBoundedToEventFlow_injective {x y : CompactTotallyBoundedUp} :
    compactTotallyBoundedToEventFlow x = compactTotallyBoundedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactTotallyBoundedFromEventFlow (compactTotallyBoundedToEventFlow x) =
        compactTotallyBoundedFromEventFlow (compactTotallyBoundedToEventFlow y) :=
    congrArg compactTotallyBoundedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactTotallyBounded_round_trip x).symm
      (Eq.trans hread (compactTotallyBounded_round_trip y)))

private theorem compactTotallyBounded_field_faithful :
    ∀ x y : CompactTotallyBoundedUp,
      compactTotallyBoundedFields x = compactTotallyBoundedFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric₁ completeMetric₁ totallyBounded₁ radiusSchedule₁ exactness₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk metric₂ completeMetric₂ totallyBounded₂ radiusSchedule₂ exactness₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance compactTotallyBoundedBHistCarrier : BHistCarrier CompactTotallyBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactTotallyBoundedToEventFlow
  fromEventFlow := compactTotallyBoundedFromEventFlow

instance compactTotallyBoundedChapterTasteGate : ChapterTasteGate CompactTotallyBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactTotallyBoundedFromEventFlow (compactTotallyBoundedToEventFlow x) = some x
    exact compactTotallyBounded_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactTotallyBoundedToEventFlow_injective heq)

instance compactTotallyBoundedFieldFaithful : FieldFaithful CompactTotallyBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactTotallyBoundedFields
  field_faithful := compactTotallyBounded_field_faithful

def taste_gate : ChapterTasteGate CompactTotallyBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactTotallyBoundedChapterTasteGate

theorem CompactTotallyBoundedTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactTotallyBoundedDecodeBHist (compactTotallyBoundedEncodeBHist h) = h) ∧
      (∀ x : CompactTotallyBoundedUp,
        compactTotallyBoundedFromEventFlow (compactTotallyBoundedToEventFlow x) = some x) ∧
        (∀ x y : CompactTotallyBoundedUp,
          compactTotallyBoundedToEventFlow x = compactTotallyBoundedToEventFlow y → x = y) ∧
          compactTotallyBoundedEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨compactTotallyBounded_decode_encode_bhist,
      compactTotallyBounded_round_trip,
      (fun _ _ heq => compactTotallyBoundedToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactTotallyBoundedUp
