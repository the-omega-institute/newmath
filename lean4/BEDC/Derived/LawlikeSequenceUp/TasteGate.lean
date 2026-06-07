import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawlikeSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Lawlike sequence packet with the seven rows displayed by the paper carrier. -/
inductive LawlikeSequenceUp : Type where
  | mk : (R W O H C P N : BHist) → LawlikeSequenceUp
  deriving DecidableEq

def lawlikeSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawlikeSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawlikeSequenceEncodeBHist h

def lawlikeSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawlikeSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawlikeSequenceDecodeBHist tail)

private theorem lawlikeSequenceDecode_encode_bhist :
    ∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lawlikeSequenceFields : LawlikeSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeSequenceUp.mk R W O H C P N => [R, W, O, H, C, P, N]

def lawlikeSequenceToEventFlow : LawlikeSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeSequenceUp.mk R W O H C P N =>
      [[BMark.b0],
        lawlikeSequenceEncodeBHist R,
        [BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist N]

def lawlikeSequenceFromEventFlow : EventFlow → Option LawlikeSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: R :: _tag1 :: W :: _tag2 :: O :: _tag3 :: H :: _tag4 :: C :: _tag5 ::
      P :: _tag6 :: N :: [] =>
      some (LawlikeSequenceUp.mk
        (lawlikeSequenceDecodeBHist R) (lawlikeSequenceDecodeBHist W)
        (lawlikeSequenceDecodeBHist O) (lawlikeSequenceDecodeBHist H)
        (lawlikeSequenceDecodeBHist C) (lawlikeSequenceDecodeBHist P)
        (lawlikeSequenceDecodeBHist N))
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
      none

private theorem lawlikeSequence_round_trip :
    ∀ x : LawlikeSequenceUp,
      lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W O H C P N =>
      change
        some
          (LawlikeSequenceUp.mk
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist R))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist W))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist O))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist H))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist C))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist P))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist N))) =
          some (LawlikeSequenceUp.mk R W O H C P N)
      rw [lawlikeSequenceDecode_encode_bhist R, lawlikeSequenceDecode_encode_bhist W,
        lawlikeSequenceDecode_encode_bhist O, lawlikeSequenceDecode_encode_bhist H,
        lawlikeSequenceDecode_encode_bhist C, lawlikeSequenceDecode_encode_bhist P,
        lawlikeSequenceDecode_encode_bhist N]

theorem lawlikeSequenceToEventFlow_injective {x y : LawlikeSequenceUp} :
    lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) =
        lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow y) :=
    congrArg lawlikeSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lawlikeSequence_round_trip x).symm
      (Eq.trans hread (lawlikeSequence_round_trip y)))

private theorem lawlikeSequence_fields_faithful :
    ∀ x y : LawlikeSequenceUp, lawlikeSequenceFields x = lawlikeSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 O1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 O2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance lawlikeSequenceBHistCarrier : BHistCarrier LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawlikeSequenceToEventFlow
  fromEventFlow := lawlikeSequenceFromEventFlow

instance lawlikeSequenceChapterTasteGate : ChapterTasteGate LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x
    exact lawlikeSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lawlikeSequenceToEventFlow_injective heq)

instance lawlikeSequenceFieldFaithful : FieldFaithful LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawlikeSequenceFields
  field_faithful := lawlikeSequence_fields_faithful

instance lawlikeSequenceNontrivial : Nontrivial LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LawlikeSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LawlikeSequenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LawlikeSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawlikeSequenceChapterTasteGate

namespace TasteGate

theorem LawlikeSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h) ∧
      (∀ x : LawlikeSequenceUp,
        lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x) ∧
      (∀ x y : LawlikeSequenceUp,
        lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y) ∧
      lawlikeSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨lawlikeSequenceDecode_encode_bhist, lawlikeSequence_round_trip,
      (fun _ _ heq => lawlikeSequenceToEventFlow_injective heq), rfl⟩

end TasteGate

end BEDC.Derived.LawlikeSequenceUp
