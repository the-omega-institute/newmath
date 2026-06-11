import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopSequenceLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopSequenceLimitUp : Type where
  | mk (S L W R D T U E H C P N : BHist) : BishopSequenceLimitUp
  deriving DecidableEq

def bishopSequenceLimitEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopSequenceLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopSequenceLimitEncodeBHist h

def bishopSequenceLimitDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopSequenceLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopSequenceLimitDecodeBHist tail)

private theorem BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopSequenceLimitFields : BishopSequenceLimitUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopSequenceLimitUp.mk S L W R D T U E H C P N => [S, L, W, R, D, T, U, E, H, C, P, N]

def bishopSequenceLimitToEventFlow : BishopSequenceLimitUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopSequenceLimitFields x).map bishopSequenceLimitEncodeBHist

def bishopSequenceLimitFromEventFlow : EventFlow -> Option BishopSequenceLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | U :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (BishopSequenceLimitUp.mk
                                                          (bishopSequenceLimitDecodeBHist S)
                                                          (bishopSequenceLimitDecodeBHist L)
                                                          (bishopSequenceLimitDecodeBHist W)
                                                          (bishopSequenceLimitDecodeBHist R)
                                                          (bishopSequenceLimitDecodeBHist D)
                                                          (bishopSequenceLimitDecodeBHist T)
                                                          (bishopSequenceLimitDecodeBHist U)
                                                          (bishopSequenceLimitDecodeBHist E)
                                                          (bishopSequenceLimitDecodeBHist H)
                                                          (bishopSequenceLimitDecodeBHist C)
                                                          (bishopSequenceLimitDecodeBHist P)
                                                          (bishopSequenceLimitDecodeBHist N))
                                                  | _ :: _ => none

private theorem BishopSequenceLimitTasteGate_single_carrier_alignment_round_trip :
    forall x : BishopSequenceLimitUp,
      bishopSequenceLimitFromEventFlow (bishopSequenceLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L W R D T U E H C P N =>
      change
        some
          (BishopSequenceLimitUp.mk
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist S))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist L))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist W))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist R))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist D))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist T))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist U))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist E))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist H))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist C))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist P))
            (bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist N))) =
          some (BishopSequenceLimitUp.mk S L W R D T U E H C P N)
      rw [BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode S,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode L,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode W,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode R,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode D,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode T,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode U,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode E,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode H,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode C,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode P,
        BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopSequenceLimitUp} :
    bishopSequenceLimitToEventFlow x = bishopSequenceLimitToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopSequenceLimitFromEventFlow (bishopSequenceLimitToEventFlow x) =
        bishopSequenceLimitFromEventFlow (bishopSequenceLimitToEventFlow y) :=
    congrArg bishopSequenceLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopSequenceLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopSequenceLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopSequenceLimitTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : BishopSequenceLimitUp,
      bishopSequenceLimitFields x = bishopSequenceLimitFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 L1 W1 R1 D1 T1 U1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 L2 W2 R2 D2 T2 U2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopSequenceLimitBHistCarrier : BHistCarrier BishopSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopSequenceLimitToEventFlow
  fromEventFlow := bishopSequenceLimitFromEventFlow

instance bishopSequenceLimitChapterTasteGate : ChapterTasteGate BishopSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopSequenceLimitFromEventFlow (bishopSequenceLimitToEventFlow x) = some x
    exact BishopSequenceLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopSequenceLimitFieldFaithful : FieldFaithful BishopSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopSequenceLimitFields
  field_faithful := BishopSequenceLimitTasteGate_single_carrier_alignment_fields_faithful

instance bishopSequenceLimitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopSequenceLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopSequenceLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def bishopSequenceLimitTasteGate : ChapterTasteGate BishopSequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopSequenceLimitChapterTasteGate

theorem BishopSequenceLimitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopSequenceLimitUp) ∧
      (∀ h : BHist,
        bishopSequenceLimitDecodeBHist (bishopSequenceLimitEncodeBHist h) = h) ∧
        (∀ x : BishopSequenceLimitUp,
          bishopSequenceLimitFromEventFlow (bishopSequenceLimitToEventFlow x) = some x) ∧
          bishopSequenceLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨bishopSequenceLimitChapterTasteGate⟩
  · constructor
    · exact BishopSequenceLimitTasteGate_single_carrier_alignment_decode_encode
    · constructor
      · exact BishopSequenceLimitTasteGate_single_carrier_alignment_round_trip
      · rfl

end BEDC.Derived.BishopSequenceLimitUp
