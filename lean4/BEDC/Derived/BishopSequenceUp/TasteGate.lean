import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopSequenceUp : Type where
  | mk (S R M D Q H C P N : BHist) : BishopSequenceUp
  deriving DecidableEq

def bishopSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopSequenceEncodeBHist h

def bishopSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopSequenceDecodeBHist tail)

private theorem BishopSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopSequenceDecodeBHist (bishopSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopSequenceFields : BishopSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopSequenceUp.mk S R M D Q H C P N => [S, R, M, D, Q, H, C, P, N]

def bishopSequenceToEventFlow : BishopSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopSequenceUp.mk S R M D Q H C P N =>
      [[BMark.b0, BMark.b1, BMark.b0, BMark.b1],
        bishopSequenceEncodeBHist S,
        bishopSequenceEncodeBHist R,
        bishopSequenceEncodeBHist M,
        bishopSequenceEncodeBHist D,
        bishopSequenceEncodeBHist Q,
        bishopSequenceEncodeBHist H,
        bishopSequenceEncodeBHist C,
        bishopSequenceEncodeBHist P,
        bishopSequenceEncodeBHist N]

def bishopSequenceFromEventFlow : EventFlow → Option BishopSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, S, R, M, D, Q, H, C, P, N] =>
      match tag with
      | [BMark.b0, BMark.b1, BMark.b0, BMark.b1] =>
          some
            (BishopSequenceUp.mk
              (bishopSequenceDecodeBHist S)
              (bishopSequenceDecodeBHist R)
              (bishopSequenceDecodeBHist M)
              (bishopSequenceDecodeBHist D)
              (bishopSequenceDecodeBHist Q)
              (bishopSequenceDecodeBHist H)
              (bishopSequenceDecodeBHist C)
              (bishopSequenceDecodeBHist P)
              (bishopSequenceDecodeBHist N))
      | _ => none
  | _ => none

private theorem BishopSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopSequenceUp,
      bishopSequenceFromEventFlow (bishopSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M D Q H C P N =>
      change
        some
            (BishopSequenceUp.mk
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist S))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist R))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist M))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist D))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist Q))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist H))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist C))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist P))
              (bishopSequenceDecodeBHist (bishopSequenceEncodeBHist N))) =
          some (BishopSequenceUp.mk S R M D Q H C P N)
      rw [BishopSequenceTasteGate_single_carrier_alignment_decode_encode S,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode R,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode M,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode D,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode Q,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode H,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode C,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode P,
        BishopSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopSequenceUp} :
    bishopSequenceToEventFlow x = bishopSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopSequenceFromEventFlow (bishopSequenceToEventFlow x) =
        bishopSequenceFromEventFlow (bishopSequenceToEventFlow y) :=
    congrArg bishopSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopSequenceUp, bishopSequenceFields x = bishopSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 M1 D1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 M2 D2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopSequenceBHistCarrier : BHistCarrier BishopSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopSequenceToEventFlow
  fromEventFlow := bishopSequenceFromEventFlow

instance bishopSequenceChapterTasteGate : ChapterTasteGate BishopSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopSequenceFromEventFlow (bishopSequenceToEventFlow x) = some x
    exact BishopSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopSequenceFieldFaithful : FieldFaithful BishopSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopSequenceFields
  field_faithful := BishopSequenceTasteGate_single_carrier_alignment_fields

instance bishopSequenceNontrivial : Nontrivial BishopSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopSequenceChapterTasteGate

theorem BishopSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopSequenceDecodeBHist (bishopSequenceEncodeBHist h) = h) ∧
      bishopSequenceFields
          (BishopSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] ∧
        bishopSequenceToEventFlow
            (BishopSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b0, BMark.b1, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨BishopSequenceTasteGate_single_carrier_alignment_decode_encode, rfl, rfl⟩

end BEDC.Derived.BishopSequenceUp
