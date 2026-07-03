import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularSequenceUp : Type where
  | mk (D W R M E H C P N : BHist) : BishopRegularSequenceUp
  deriving DecidableEq

def bishopRegularSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularSequenceEncodeBHist h

def bishopRegularSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularSequenceDecodeBHist tail)

private theorem BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularSequenceFields : BishopRegularSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularSequenceUp.mk D W R M E H C P N => [D, W, R, M, E, H, C, P, N]

def bishopRegularSequenceToEventFlow : BishopRegularSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRegularSequenceFields x).map bishopRegularSequenceEncodeBHist

def bishopRegularSequenceFromEventFlow : EventFlow → Option BishopRegularSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (BishopRegularSequenceUp.mk
                                              (bishopRegularSequenceDecodeBHist D)
                                              (bishopRegularSequenceDecodeBHist W)
                                              (bishopRegularSequenceDecodeBHist R)
                                              (bishopRegularSequenceDecodeBHist M)
                                              (bishopRegularSequenceDecodeBHist E)
                                              (bishopRegularSequenceDecodeBHist H)
                                              (bishopRegularSequenceDecodeBHist C)
                                              (bishopRegularSequenceDecodeBHist P)
                                              (bishopRegularSequenceDecodeBHist N))
                                      | _ :: _ => none

private theorem BishopRegularSequenceTasteGate_single_carrier_alignment_round_trip
    (x : BishopRegularSequenceUp) :
    bishopRegularSequenceFromEventFlow (bishopRegularSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W R M E H C P N =>
      change
        some
          (BishopRegularSequenceUp.mk
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist D))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist W))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist R))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist M))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist E))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist H))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist C))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist P))
            (bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist N))) =
          some (BishopRegularSequenceUp.mk D W R M E H C P N)
      rw [BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode D,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode W,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode R,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode M,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode E,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode H,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode C,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode P,
        BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRegularSequenceTasteGate_single_carrier_alignment_injective
    {x y : BishopRegularSequenceUp} :
    bishopRegularSequenceToEventFlow x = bishopRegularSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularSequenceFromEventFlow (bishopRegularSequenceToEventFlow x) =
        bishopRegularSequenceFromEventFlow (bishopRegularSequenceToEventFlow y) :=
    congrArg bishopRegularSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopRegularSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRegularSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopRegularSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopRegularSequenceUp,
      bishopRegularSequenceFields x = bishopRegularSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ R₁ M₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ R₂ M₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopRegularSequenceBHistCarrier : BHistCarrier BishopRegularSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularSequenceToEventFlow
  fromEventFlow := bishopRegularSequenceFromEventFlow

instance bishopRegularSequenceChapterTasteGate : ChapterTasteGate BishopRegularSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRegularSequenceFromEventFlow (bishopRegularSequenceToEventFlow x) = some x
    exact BishopRegularSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopRegularSequenceTasteGate_single_carrier_alignment_injective heq)

instance bishopRegularSequenceFieldFaithful : FieldFaithful BishopRegularSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRegularSequenceFields
  field_faithful := BishopRegularSequenceTasteGate_single_carrier_alignment_fields

instance bishopRegularSequenceNontrivial : Nontrivial BishopRegularSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRegularSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRegularSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopRegularSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRegularSequenceChapterTasteGate

theorem BishopRegularSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRegularSequenceDecodeBHist (bishopRegularSequenceEncodeBHist h) = h) ∧
      (∀ x : BishopRegularSequenceUp,
        bishopRegularSequenceFromEventFlow (bishopRegularSequenceToEventFlow x) = some x) ∧
        (∀ x y : BishopRegularSequenceUp,
          bishopRegularSequenceToEventFlow x = bishopRegularSequenceToEventFlow y → x = y) ∧
          bishopRegularSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  constructor
  · exact BishopRegularSequenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact BishopRegularSequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BishopRegularSequenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.BishopRegularSequenceUp
