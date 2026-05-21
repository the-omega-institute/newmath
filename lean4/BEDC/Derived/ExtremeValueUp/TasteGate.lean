import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExtremeValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExtremeValueUp : Type where
  | mk (X F U M S R H C P N : BHist) : ExtremeValueUp
  deriving DecidableEq

def extremeValueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: extremeValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: extremeValueEncodeBHist h

def extremeValueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (extremeValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (extremeValueDecodeBHist tail)

private theorem extremeValue_decode_encode_bhist :
    ∀ h : BHist, extremeValueDecodeBHist (extremeValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def extremeValueFields : ExtremeValueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExtremeValueUp.mk X F U M S R H C P N => [X, F, U, M, S, R, H, C, P, N]

def extremeValueToEventFlow : ExtremeValueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ExtremeValueUp.mk X F U M S R H C P N =>
      [extremeValueEncodeBHist X,
        extremeValueEncodeBHist F,
        extremeValueEncodeBHist U,
        extremeValueEncodeBHist M,
        extremeValueEncodeBHist S,
        extremeValueEncodeBHist R,
        extremeValueEncodeBHist H,
        extremeValueEncodeBHist C,
        extremeValueEncodeBHist P,
        extremeValueEncodeBHist N]

private def extremeValueRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => extremeValueRawAt n rest

private def extremeValueLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => extremeValueLengthEq n rest

def extremeValueFromEventFlow : EventFlow → Option ExtremeValueUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match extremeValueLengthEq 10 flow with
      | true =>
          some
            (ExtremeValueUp.mk
              (extremeValueDecodeBHist (extremeValueRawAt 0 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 1 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 2 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 3 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 4 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 5 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 6 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 7 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 8 flow))
              (extremeValueDecodeBHist (extremeValueRawAt 9 flow)))
      | false => none

private theorem extremeValue_round_trip :
    ∀ x : ExtremeValueUp,
      extremeValueFromEventFlow (extremeValueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F U M S R H C P N =>
      change
        some
          (ExtremeValueUp.mk
            (extremeValueDecodeBHist (extremeValueEncodeBHist X))
            (extremeValueDecodeBHist (extremeValueEncodeBHist F))
            (extremeValueDecodeBHist (extremeValueEncodeBHist U))
            (extremeValueDecodeBHist (extremeValueEncodeBHist M))
            (extremeValueDecodeBHist (extremeValueEncodeBHist S))
            (extremeValueDecodeBHist (extremeValueEncodeBHist R))
            (extremeValueDecodeBHist (extremeValueEncodeBHist H))
            (extremeValueDecodeBHist (extremeValueEncodeBHist C))
            (extremeValueDecodeBHist (extremeValueEncodeBHist P))
            (extremeValueDecodeBHist (extremeValueEncodeBHist N))) =
          some (ExtremeValueUp.mk X F U M S R H C P N)
      rw [extremeValue_decode_encode_bhist X,
        extremeValue_decode_encode_bhist F,
        extremeValue_decode_encode_bhist U,
        extremeValue_decode_encode_bhist M,
        extremeValue_decode_encode_bhist S,
        extremeValue_decode_encode_bhist R,
        extremeValue_decode_encode_bhist H,
        extremeValue_decode_encode_bhist C,
        extremeValue_decode_encode_bhist P,
        extremeValue_decode_encode_bhist N]

private theorem extremeValueToEventFlow_injective {x y : ExtremeValueUp} :
    extremeValueToEventFlow x = extremeValueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      extremeValueFromEventFlow (extremeValueToEventFlow x) =
        extremeValueFromEventFlow (extremeValueToEventFlow y) :=
    congrArg extremeValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (extremeValue_round_trip x).symm
      (Eq.trans hread (extremeValue_round_trip y)))

private theorem extremeValue_field_faithful :
    ∀ x y : ExtremeValueUp, extremeValueFields x = extremeValueFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X1 F1 U1 M1 S1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 U2 M2 S2 R2 H2 C2 P2 N2 =>
          cases h
          rfl

instance extremeValueBHistCarrier : BHistCarrier ExtremeValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := extremeValueToEventFlow
  fromEventFlow := extremeValueFromEventFlow

instance extremeValueChapterTasteGate : ChapterTasteGate ExtremeValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change extremeValueFromEventFlow (extremeValueToEventFlow x) = some x
    exact extremeValue_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (extremeValueToEventFlow_injective heq)

instance extremeValueFieldFaithful : FieldFaithful ExtremeValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := extremeValueFields
  field_faithful := extremeValue_field_faithful

instance extremeValueNontrivial : Nontrivial ExtremeValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExtremeValueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExtremeValueUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ExtremeValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  extremeValueChapterTasteGate

theorem ExtremeValueTasteGate_single_carrier_alignment :
    (∀ h : BHist, extremeValueDecodeBHist (extremeValueEncodeBHist h) = h) ∧
      (∀ x : ExtremeValueUp,
        extremeValueFromEventFlow (extremeValueToEventFlow x) = some x) ∧
        (∀ x y : ExtremeValueUp,
          extremeValueToEventFlow x = extremeValueToEventFlow y → x = y) ∧
          extremeValueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨extremeValue_decode_encode_bhist,
      extremeValue_round_trip,
      by
        intro x y heq
        exact extremeValueToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ExtremeValueUp
