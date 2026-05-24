import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalExtractionUp : Type where
  | mk (f delta w d q e h c p n : BHist) : RegularCauchyDiagonalExtractionUp
  deriving DecidableEq

def regularCauchyDiagonalExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalExtractionEncodeBHist h

def regularCauchyDiagonalExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalExtractionDecodeBHist tail)

private theorem regularCauchyDiagonalExtraction_decode_encode_bhist :
    ∀ h : BHist, regularCauchyDiagonalExtractionDecodeBHist
      (regularCauchyDiagonalExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalExtractionToEventFlow :
    RegularCauchyDiagonalExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalExtractionUp.mk f delta w d q e h c p n =>
      [[BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist f,
        [BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist delta,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalExtractionEncodeBHist n]

private def regularCauchyDiagonalExtractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDiagonalExtractionEventAtDefault index rest

def regularCauchyDiagonalExtractionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyDiagonalExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDiagonalExtractionUp.mk
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 1 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 3 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 5 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 7 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 9 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 11 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 13 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 15 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 17 ef))
      (regularCauchyDiagonalExtractionDecodeBHist
        (regularCauchyDiagonalExtractionEventAtDefault 19 ef)))

private theorem regularCauchyDiagonalExtraction_round_trip :
    ∀ x : RegularCauchyDiagonalExtractionUp,
      regularCauchyDiagonalExtractionFromEventFlow
          (regularCauchyDiagonalExtractionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk f delta w d q e h c p n =>
      change
        some
          (RegularCauchyDiagonalExtractionUp.mk
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist f))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist delta))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist w))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist d))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist q))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist e))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist h))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist c))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist p))
            (regularCauchyDiagonalExtractionDecodeBHist
              (regularCauchyDiagonalExtractionEncodeBHist n))) =
          some (RegularCauchyDiagonalExtractionUp.mk f delta w d q e h c p n)
      rw [regularCauchyDiagonalExtraction_decode_encode_bhist f,
        regularCauchyDiagonalExtraction_decode_encode_bhist delta,
        regularCauchyDiagonalExtraction_decode_encode_bhist w,
        regularCauchyDiagonalExtraction_decode_encode_bhist d,
        regularCauchyDiagonalExtraction_decode_encode_bhist q,
        regularCauchyDiagonalExtraction_decode_encode_bhist e,
        regularCauchyDiagonalExtraction_decode_encode_bhist h,
        regularCauchyDiagonalExtraction_decode_encode_bhist c,
        regularCauchyDiagonalExtraction_decode_encode_bhist p,
        regularCauchyDiagonalExtraction_decode_encode_bhist n]

private theorem regularCauchyDiagonalExtractionToEventFlow_injective
    {x y : RegularCauchyDiagonalExtractionUp} :
    regularCauchyDiagonalExtractionToEventFlow x =
      regularCauchyDiagonalExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalExtractionFromEventFlow
          (regularCauchyDiagonalExtractionToEventFlow x) =
        regularCauchyDiagonalExtractionFromEventFlow
          (regularCauchyDiagonalExtractionToEventFlow y) :=
    congrArg regularCauchyDiagonalExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDiagonalExtraction_round_trip x).symm
      (Eq.trans hread (regularCauchyDiagonalExtraction_round_trip y)))

private def regularCauchyDiagonalExtractionFields :
    RegularCauchyDiagonalExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalExtractionUp.mk f delta w d q e h c p n =>
      [f, delta, w, d, q, e, h, c, p, n]

private theorem regularCauchyDiagonalExtraction_field_faithful :
    ∀ x y : RegularCauchyDiagonalExtractionUp,
      regularCauchyDiagonalExtractionFields x =
        regularCauchyDiagonalExtractionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token₁ token₂ hfields
  cases token₁ with
  | mk f₁ delta₁ w₁ d₁ q₁ e₁ h₁ c₁ p₁ n₁ =>
      cases token₂ with
      | mk f₂ delta₂ w₂ d₂ q₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance regularCauchyDiagonalExtractionBHistCarrier :
    BHistCarrier RegularCauchyDiagonalExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalExtractionToEventFlow
  fromEventFlow := regularCauchyDiagonalExtractionFromEventFlow

instance regularCauchyDiagonalExtractionChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalExtractionFromEventFlow
          (regularCauchyDiagonalExtractionToEventFlow x) =
        some x
    exact regularCauchyDiagonalExtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalExtractionToEventFlow_injective heq)

instance regularCauchyDiagonalExtractionFieldFaithful :
    FieldFaithful RegularCauchyDiagonalExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyDiagonalExtractionFields
  field_faithful := regularCauchyDiagonalExtraction_field_faithful

instance regularCauchyDiagonalExtractionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyDiagonalExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyDiagonalExtractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyDiagonalExtractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyDiagonalExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDiagonalExtractionChapterTasteGate

private theorem RegularCauchyDiagonalExtractionTasteGate_single_carrier_alignment_instances :
    Nonempty (ChapterTasteGate RegularCauchyDiagonalExtractionUp) ∧
      Nonempty (FieldFaithful RegularCauchyDiagonalExtractionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyDiagonalExtractionUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨regularCauchyDiagonalExtractionChapterTasteGate⟩,
      ⟨regularCauchyDiagonalExtractionFieldFaithful⟩,
      ⟨regularCauchyDiagonalExtractionNontrivial⟩⟩

theorem RegularCauchyDiagonalExtractionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyDiagonalExtractionUp) ∧
      Nonempty (FieldFaithful RegularCauchyDiagonalExtractionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyDiagonalExtractionUp) ∧
          (∀ h : BHist,
            regularCauchyDiagonalExtractionDecodeBHist
                (regularCauchyDiagonalExtractionEncodeBHist h) =
              h) ∧
            (∀ x : RegularCauchyDiagonalExtractionUp,
              regularCauchyDiagonalExtractionFromEventFlow
                  (regularCauchyDiagonalExtractionToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyDiagonalExtractionUp,
                regularCauchyDiagonalExtractionToEventFlow x =
                  regularCauchyDiagonalExtractionToEventFlow y → x = y) ∧
                regularCauchyDiagonalExtractionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  have hinstances :=
    RegularCauchyDiagonalExtractionTasteGate_single_carrier_alignment_instances
  exact
    ⟨hinstances.1,
      hinstances.2.1,
      hinstances.2.2,
      regularCauchyDiagonalExtraction_decode_encode_bhist,
      regularCauchyDiagonalExtraction_round_trip,
      (fun _ _ heq => regularCauchyDiagonalExtractionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyDiagonalExtractionUp
