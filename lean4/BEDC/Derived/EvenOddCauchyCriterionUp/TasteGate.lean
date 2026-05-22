import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EvenOddCauchyCriterionUp : Type where
  | mk
      (evenRow oddRow evenSchedule oddSchedule selector sharedModulus dyadicTolerance
        fusion realHandoff transport replay provenance localName : BHist) :
      EvenOddCauchyCriterionUp

def evenOddCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: evenOddCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: evenOddCauchyCriterionEncodeBHist h

def evenOddCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (evenOddCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (evenOddCauchyCriterionDecodeBHist tail)

private theorem evenOddCauchyCriterion_decode_encode_bhist :
    ∀ h : BHist,
      evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def evenOddCauchyCriterionFields : EvenOddCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EvenOddCauchyCriterionUp.mk evenRow oddRow evenSchedule oddSchedule selector
      sharedModulus dyadicTolerance fusion realHandoff transport replay provenance localName =>
      [evenRow, oddRow, evenSchedule, oddSchedule, selector, sharedModulus, dyadicTolerance,
        fusion, realHandoff, transport, replay, provenance, localName]

def evenOddCauchyCriterionToEventFlow : EvenOddCauchyCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (evenOddCauchyCriterionFields x).map evenOddCauchyCriterionEncodeBHist

private def evenOddCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => evenOddCauchyCriterionEventAtDefault index rest

def evenOddCauchyCriterionFromEventFlow
    (flow : EventFlow) : Option EvenOddCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EvenOddCauchyCriterionUp.mk
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 0 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 1 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 2 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 3 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 4 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 5 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 6 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 7 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 8 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 9 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 10 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 11 flow))
      (evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEventAtDefault 12 flow)))

private theorem evenOddCauchyCriterion_round_trip :
    ∀ x : EvenOddCauchyCriterionUp,
      evenOddCauchyCriterionFromEventFlow
        (evenOddCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk evenRow oddRow evenSchedule oddSchedule selector sharedModulus dyadicTolerance fusion
      realHandoff transport replay provenance localName =>
      change
        some
          (EvenOddCauchyCriterionUp.mk
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist evenRow))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist oddRow))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist evenSchedule))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist oddSchedule))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist selector))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist sharedModulus))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist dyadicTolerance))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist fusion))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist realHandoff))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist transport))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist replay))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist provenance))
            (evenOddCauchyCriterionDecodeBHist
              (evenOddCauchyCriterionEncodeBHist localName))) =
          some
            (EvenOddCauchyCriterionUp.mk evenRow oddRow evenSchedule oddSchedule selector
              sharedModulus dyadicTolerance fusion realHandoff transport replay provenance
              localName)
      rw [evenOddCauchyCriterion_decode_encode_bhist evenRow,
        evenOddCauchyCriterion_decode_encode_bhist oddRow,
        evenOddCauchyCriterion_decode_encode_bhist evenSchedule,
        evenOddCauchyCriterion_decode_encode_bhist oddSchedule,
        evenOddCauchyCriterion_decode_encode_bhist selector,
        evenOddCauchyCriterion_decode_encode_bhist sharedModulus,
        evenOddCauchyCriterion_decode_encode_bhist dyadicTolerance,
        evenOddCauchyCriterion_decode_encode_bhist fusion,
        evenOddCauchyCriterion_decode_encode_bhist realHandoff,
        evenOddCauchyCriterion_decode_encode_bhist transport,
        evenOddCauchyCriterion_decode_encode_bhist replay,
        evenOddCauchyCriterion_decode_encode_bhist provenance,
        evenOddCauchyCriterion_decode_encode_bhist localName]

private theorem evenOddCauchyCriterionToEventFlow_injective
    {x y : EvenOddCauchyCriterionUp} :
    evenOddCauchyCriterionToEventFlow x = evenOddCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      evenOddCauchyCriterionFromEventFlow (evenOddCauchyCriterionToEventFlow x) =
        evenOddCauchyCriterionFromEventFlow (evenOddCauchyCriterionToEventFlow y) :=
    congrArg evenOddCauchyCriterionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (evenOddCauchyCriterion_round_trip x).symm
        (Eq.trans hread (evenOddCauchyCriterion_round_trip y)))

private theorem evenOddCauchyCriterion_fields_faithful :
    ∀ x y : EvenOddCauchyCriterionUp,
      evenOddCauchyCriterionFields x = evenOddCauchyCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk evenRow₁ oddRow₁ evenSchedule₁ oddSchedule₁ selector₁ sharedModulus₁
      dyadicTolerance₁ fusion₁ realHandoff₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk evenRow₂ oddRow₂ evenSchedule₂ oddSchedule₂ selector₂ sharedModulus₂
          dyadicTolerance₂ fusion₂ realHandoff₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance evenOddCauchyCriterionBHistCarrier :
    BHistCarrier EvenOddCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := evenOddCauchyCriterionToEventFlow
  fromEventFlow := evenOddCauchyCriterionFromEventFlow

instance evenOddCauchyCriterionChapterTasteGate :
    ChapterTasteGate EvenOddCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      evenOddCauchyCriterionFromEventFlow
        (evenOddCauchyCriterionToEventFlow x) = some x
    exact evenOddCauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (evenOddCauchyCriterionToEventFlow_injective heq)

instance evenOddCauchyCriterionFieldFaithful :
    FieldFaithful EvenOddCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := evenOddCauchyCriterionFields
  field_faithful := evenOddCauchyCriterion_fields_faithful

instance evenOddCauchyCriterionNontrivial :
    Nontrivial EvenOddCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EvenOddCauchyCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EvenOddCauchyCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EvenOddCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  evenOddCauchyCriterionChapterTasteGate

def taste_gate_witness : FieldFaithful EvenOddCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  evenOddCauchyCriterionFieldFaithful

theorem EvenOddCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      evenOddCauchyCriterionDecodeBHist (evenOddCauchyCriterionEncodeBHist h) = h) ∧
      (∀ x : EvenOddCauchyCriterionUp,
        evenOddCauchyCriterionFromEventFlow (evenOddCauchyCriterionToEventFlow x) = some x) ∧
        (∀ x y : EvenOddCauchyCriterionUp,
          evenOddCauchyCriterionToEventFlow x = evenOddCauchyCriterionToEventFlow y →
            x = y) ∧
          evenOddCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨evenOddCauchyCriterion_decode_encode_bhist,
      evenOddCauchyCriterion_round_trip,
      (fun _ _ heq => evenOddCauchyCriterionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
