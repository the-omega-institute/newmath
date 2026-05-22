import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterRefinementUp : Type where
  | mk (source target cofinal reverse transport replay provenance localName : BHist) :
      FilterRefinementUp

def filterRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterRefinementEncodeBHist h

def filterRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterRefinementDecodeBHist tail)

private theorem filterRefinement_decode_encode_bhist :
    ∀ h : BHist, filterRefinementDecodeBHist (filterRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def filterRefinementFields : FilterRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterRefinementUp.mk source target cofinal reverse transport replay provenance
      localName =>
      [source, target, cofinal, reverse, transport, replay, provenance, localName]

def filterRefinementToEventFlow : FilterRefinementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (filterRefinementFields x).map filterRefinementEncodeBHist

private def filterRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filterRefinementEventAtDefault index rest

def filterRefinementFromEventFlow (flow : EventFlow) : Option FilterRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilterRefinementUp.mk
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 0 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 1 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 2 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 3 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 4 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 5 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 6 flow))
      (filterRefinementDecodeBHist (filterRefinementEventAtDefault 7 flow)))

private theorem filterRefinement_round_trip :
    ∀ x : FilterRefinementUp,
      filterRefinementFromEventFlow (filterRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target cofinal reverse transport replay provenance localName =>
      change
        some
          (FilterRefinementUp.mk
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist source))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist target))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist cofinal))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist reverse))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist transport))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist replay))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist provenance))
            (filterRefinementDecodeBHist (filterRefinementEncodeBHist localName))) =
          some
            (FilterRefinementUp.mk source target cofinal reverse transport replay provenance
              localName)
      rw [filterRefinement_decode_encode_bhist source,
        filterRefinement_decode_encode_bhist target,
        filterRefinement_decode_encode_bhist cofinal,
        filterRefinement_decode_encode_bhist reverse,
        filterRefinement_decode_encode_bhist transport,
        filterRefinement_decode_encode_bhist replay,
        filterRefinement_decode_encode_bhist provenance,
        filterRefinement_decode_encode_bhist localName]

private theorem filterRefinementToEventFlow_injective
    {x y : FilterRefinementUp} :
    filterRefinementToEventFlow x = filterRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterRefinementFromEventFlow (filterRefinementToEventFlow x) =
        filterRefinementFromEventFlow (filterRefinementToEventFlow y) :=
    congrArg filterRefinementFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (filterRefinement_round_trip x).symm
        (Eq.trans hread (filterRefinement_round_trip y)))

private theorem filterRefinement_fields_faithful :
    ∀ x y : FilterRefinementUp, filterRefinementFields x = filterRefinementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ target₁ cofinal₁ reverse₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk source₂ target₂ cofinal₂ reverse₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance filterRefinementBHistCarrier : BHistCarrier FilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterRefinementToEventFlow
  fromEventFlow := filterRefinementFromEventFlow

instance filterRefinementChapterTasteGate :
    ChapterTasteGate FilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change filterRefinementFromEventFlow (filterRefinementToEventFlow x) = some x
    exact filterRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (filterRefinementToEventFlow_injective heq)

instance filterRefinementFieldFaithful :
    FieldFaithful FilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := filterRefinementFields
  field_faithful := filterRefinement_fields_faithful

instance filterRefinementNontrivial : Nontrivial FilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FilterRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FilterRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FilterRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterRefinementChapterTasteGate

def taste_gate_witness : FieldFaithful FilterRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterRefinementFieldFaithful

theorem FilterRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist, filterRefinementDecodeBHist (filterRefinementEncodeBHist h) = h) ∧
      (∀ x : FilterRefinementUp,
        filterRefinementFromEventFlow (filterRefinementToEventFlow x) = some x) ∧
        (∀ x y : FilterRefinementUp,
          filterRefinementToEventFlow x = filterRefinementToEventFlow y → x = y) ∧
          filterRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨filterRefinement_decode_encode_bhist,
      filterRefinement_round_trip,
      (fun _ _ heq => filterRefinementToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FilterRefinementUp
