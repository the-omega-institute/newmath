import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LawlessSequenceUp : Type where
  | mk (W B I H C P N : BHist) : LawlessSequenceUp
  deriving DecidableEq

def lawlessSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawlessSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawlessSequenceEncodeBHist h

def lawlessSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawlessSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawlessSequenceDecodeBHist tail)

private theorem lawlessSequence_decode_encode_bhist :
    ∀ h : BHist, lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lawlessSequenceFields : LawlessSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LawlessSequenceUp.mk W B I H C P N => [W, B, I, H, C, P, N]

def lawlessSequenceToEventFlow : LawlessSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LawlessSequenceUp.mk W B I H C P N =>
      [lawlessSequenceEncodeBHist W,
        lawlessSequenceEncodeBHist B,
        lawlessSequenceEncodeBHist I,
        lawlessSequenceEncodeBHist H,
        lawlessSequenceEncodeBHist C,
        lawlessSequenceEncodeBHist P,
        lawlessSequenceEncodeBHist N]

private def lawlessSequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => lawlessSequenceRawAt n rest

private def lawlessSequenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => lawlessSequenceLengthEq n rest

def lawlessSequenceFromEventFlow : EventFlow → Option LawlessSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match lawlessSequenceLengthEq 7 flow with
      | true =>
          some
            (LawlessSequenceUp.mk
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 0 flow))
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 1 flow))
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 2 flow))
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 3 flow))
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 4 flow))
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 5 flow))
              (lawlessSequenceDecodeBHist (lawlessSequenceRawAt 6 flow)))
      | false => none

private theorem lawlessSequence_round_trip :
    ∀ x : LawlessSequenceUp,
      lawlessSequenceFromEventFlow (lawlessSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W B I H C P N =>
      change
        some
          (LawlessSequenceUp.mk
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist W))
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist B))
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist I))
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist H))
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist C))
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist P))
            (lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist N))) =
          some (LawlessSequenceUp.mk W B I H C P N)
      rw [lawlessSequence_decode_encode_bhist W,
        lawlessSequence_decode_encode_bhist B,
        lawlessSequence_decode_encode_bhist I,
        lawlessSequence_decode_encode_bhist H,
        lawlessSequence_decode_encode_bhist C,
        lawlessSequence_decode_encode_bhist P,
        lawlessSequence_decode_encode_bhist N]

private theorem lawlessSequenceToEventFlow_injective {x y : LawlessSequenceUp} :
    lawlessSequenceToEventFlow x = lawlessSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lawlessSequenceFromEventFlow (lawlessSequenceToEventFlow x) =
        lawlessSequenceFromEventFlow (lawlessSequenceToEventFlow y) :=
    congrArg lawlessSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lawlessSequence_round_trip x).symm
      (Eq.trans hread (lawlessSequence_round_trip y)))

private theorem lawlessSequence_field_faithful :
    ∀ x y : LawlessSequenceUp, lawlessSequenceFields x = lawlessSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk W1 B1 I1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 B2 I2 H2 C2 P2 N2 =>
          cases h
          rfl

instance lawlessSequenceBHistCarrier : BHistCarrier LawlessSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawlessSequenceToEventFlow
  fromEventFlow := lawlessSequenceFromEventFlow

instance lawlessSequenceChapterTasteGate : ChapterTasteGate LawlessSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawlessSequenceFromEventFlow (lawlessSequenceToEventFlow x) = some x
    exact lawlessSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lawlessSequenceToEventFlow_injective heq)

instance lawlessSequenceFieldFaithful : FieldFaithful LawlessSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawlessSequenceFields
  field_faithful := lawlessSequence_field_faithful

instance lawlessSequenceNontrivial : Nontrivial LawlessSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LawlessSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LawlessSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LawlessSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawlessSequenceChapterTasteGate

theorem LawlessSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawlessSequenceDecodeBHist (lawlessSequenceEncodeBHist h) = h) ∧
      (∀ x : LawlessSequenceUp,
        lawlessSequenceFromEventFlow (lawlessSequenceToEventFlow x) = some x) ∧
        (∀ x y : LawlessSequenceUp,
          lawlessSequenceToEventFlow x = lawlessSequenceToEventFlow y → x = y) ∧
          lawlessSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨lawlessSequence_decode_encode_bhist,
      lawlessSequence_round_trip,
      by
        intro x y heq
        exact lawlessSequenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LawlessSequenceUp
