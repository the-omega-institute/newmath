import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JordanContentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive JordanContentUp : Type where
  | mk (B P L U R S H C Q N : BHist) : JordanContentUp

def jordanContentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jordanContentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jordanContentEncodeBHist h

def jordanContentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jordanContentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jordanContentDecodeBHist tail)

private theorem JordanContentTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, jordanContentDecodeBHist (jordanContentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def jordanContentFields : JordanContentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JordanContentUp.mk B P L U R S H C Q N => [B, P, L, U, R, S, H, C, Q, N]

def jordanContentToEventFlow : JordanContentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (jordanContentFields x).map jordanContentEncodeBHist

private def jordanContentRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => jordanContentRawAt n rest

private def jordanContentLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => jordanContentLengthEq n rest

def jordanContentFromEventFlow : EventFlow → Option JordanContentUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match jordanContentLengthEq 10 flow with
      | true =>
          some
            (JordanContentUp.mk
              (jordanContentDecodeBHist (jordanContentRawAt 0 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 1 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 2 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 3 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 4 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 5 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 6 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 7 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 8 flow))
              (jordanContentDecodeBHist (jordanContentRawAt 9 flow)))
      | false => none

private theorem JordanContentTasteGate_single_carrier_alignment_round_trip :
    ∀ x : JordanContentUp,
      jordanContentFromEventFlow (jordanContentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B P L U R S H C Q N =>
      change
        some
          (JordanContentUp.mk
            (jordanContentDecodeBHist (jordanContentEncodeBHist B))
            (jordanContentDecodeBHist (jordanContentEncodeBHist P))
            (jordanContentDecodeBHist (jordanContentEncodeBHist L))
            (jordanContentDecodeBHist (jordanContentEncodeBHist U))
            (jordanContentDecodeBHist (jordanContentEncodeBHist R))
            (jordanContentDecodeBHist (jordanContentEncodeBHist S))
            (jordanContentDecodeBHist (jordanContentEncodeBHist H))
            (jordanContentDecodeBHist (jordanContentEncodeBHist C))
            (jordanContentDecodeBHist (jordanContentEncodeBHist Q))
            (jordanContentDecodeBHist (jordanContentEncodeBHist N))) =
          some (JordanContentUp.mk B P L U R S H C Q N)
      rw [JordanContentTasteGate_single_carrier_alignment_decode_encode B,
        JordanContentTasteGate_single_carrier_alignment_decode_encode P,
        JordanContentTasteGate_single_carrier_alignment_decode_encode L,
        JordanContentTasteGate_single_carrier_alignment_decode_encode U,
        JordanContentTasteGate_single_carrier_alignment_decode_encode R,
        JordanContentTasteGate_single_carrier_alignment_decode_encode S,
        JordanContentTasteGate_single_carrier_alignment_decode_encode H,
        JordanContentTasteGate_single_carrier_alignment_decode_encode C,
        JordanContentTasteGate_single_carrier_alignment_decode_encode Q,
        JordanContentTasteGate_single_carrier_alignment_decode_encode N]

private theorem JordanContentTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : JordanContentUp} :
    jordanContentToEventFlow x = jordanContentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jordanContentFromEventFlow (jordanContentToEventFlow x) =
        jordanContentFromEventFlow (jordanContentToEventFlow y) :=
    congrArg jordanContentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (JordanContentTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (JordanContentTasteGate_single_carrier_alignment_round_trip y)))

private theorem JordanContentTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : JordanContentUp, jordanContentFields x = jordanContentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B P L U R S H C Q N =>
      cases y with
      | mk B' P' L' U' R' S' H' C' Q' N' =>
          cases hfields
          rfl

instance jordanContentBHistCarrier : BHistCarrier JordanContentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jordanContentToEventFlow
  fromEventFlow := jordanContentFromEventFlow

instance jordanContentChapterTasteGate : ChapterTasteGate JordanContentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change jordanContentFromEventFlow (jordanContentToEventFlow x) = some x
    exact JordanContentTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (JordanContentTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance jordanContentFieldFaithful : FieldFaithful JordanContentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := jordanContentFields
  field_faithful := JordanContentTasteGate_single_carrier_alignment_fields_faithful

instance jordanContentNontrivial : BEDC.Meta.TasteGate.Nontrivial JordanContentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨JordanContentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      JordanContentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def JordanContentTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate JordanContentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  jordanContentChapterTasteGate

theorem JordanContentTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate JordanContentUp) ∧
      Nonempty (FieldFaithful JordanContentUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial JordanContentUp) ∧
      (∀ h : BHist, jordanContentDecodeBHist (jordanContentEncodeBHist h) = h) ∧
      (∀ x : JordanContentUp,
        jordanContentFromEventFlow (jordanContentToEventFlow x) = some x) ∧
      (∀ x y : JordanContentUp,
        jordanContentToEventFlow x = jordanContentToEventFlow y → x = y) ∧
      jordanContentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨jordanContentChapterTasteGate⟩
  constructor
  · exact ⟨jordanContentFieldFaithful⟩
  constructor
  · exact ⟨jordanContentNontrivial⟩
  constructor
  · exact JordanContentTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact JordanContentTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact JordanContentTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.JordanContentUp
