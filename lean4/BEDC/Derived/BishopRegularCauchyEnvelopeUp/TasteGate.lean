import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularCauchyEnvelopeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularCauchyEnvelopeUp : Type where
  | mk (W R D S H C P N : BHist) : BishopRegularCauchyEnvelopeUp
  deriving DecidableEq

private def bishopRegularCauchyEnvelopeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularCauchyEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularCauchyEnvelopeEncodeBHist h

private def bishopRegularCauchyEnvelopeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularCauchyEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularCauchyEnvelopeDecodeBHist tail)

private theorem bishopRegularCauchyEnvelope_decode_encode_bhist :
    forall h : BHist,
      bishopRegularCauchyEnvelopeDecodeBHist
        (bishopRegularCauchyEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def bishopRegularCauchyEnvelopeToEventFlow :
    BishopRegularCauchyEnvelopeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularCauchyEnvelopeUp.mk W R D S H C P N =>
      [[BMark.b0], bishopRegularCauchyEnvelopeEncodeBHist W,
        [BMark.b1, BMark.b0], bishopRegularCauchyEnvelopeEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0], bishopRegularCauchyEnvelopeEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularCauchyEnvelopeEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularCauchyEnvelopeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularCauchyEnvelopeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularCauchyEnvelopeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopRegularCauchyEnvelopeEncodeBHist N]

private def bishopRegularCauchyEnvelopeFromEventFlow :
    EventFlow -> Option BishopRegularCauchyEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (BishopRegularCauchyEnvelopeUp.mk
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            W)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            R)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            D)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            S)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            H)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            C)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            P)
                                                                          (bishopRegularCauchyEnvelopeDecodeBHist
                                                                            N))
                                                                  | _ :: _ => none

private theorem bishopRegularCauchyEnvelope_round_trip :
    forall x : BishopRegularCauchyEnvelopeUp,
      bishopRegularCauchyEnvelopeFromEventFlow
        (bishopRegularCauchyEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D S H C P N =>
      change
        some
          (BishopRegularCauchyEnvelopeUp.mk
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist W))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist R))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist D))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist S))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist H))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist C))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist P))
            (bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist N))) =
          some (BishopRegularCauchyEnvelopeUp.mk W R D S H C P N)
      rw [bishopRegularCauchyEnvelope_decode_encode_bhist W,
        bishopRegularCauchyEnvelope_decode_encode_bhist R,
        bishopRegularCauchyEnvelope_decode_encode_bhist D,
        bishopRegularCauchyEnvelope_decode_encode_bhist S,
        bishopRegularCauchyEnvelope_decode_encode_bhist H,
        bishopRegularCauchyEnvelope_decode_encode_bhist C,
        bishopRegularCauchyEnvelope_decode_encode_bhist P,
        bishopRegularCauchyEnvelope_decode_encode_bhist N]

private theorem bishopRegularCauchyEnvelopeToEventFlow_injective
    {x y : BishopRegularCauchyEnvelopeUp} :
    bishopRegularCauchyEnvelopeToEventFlow x =
      bishopRegularCauchyEnvelopeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularCauchyEnvelopeFromEventFlow
          (bishopRegularCauchyEnvelopeToEventFlow x) =
        bishopRegularCauchyEnvelopeFromEventFlow
          (bishopRegularCauchyEnvelopeToEventFlow y) :=
    congrArg bishopRegularCauchyEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRegularCauchyEnvelope_round_trip x).symm
      (Eq.trans hread (bishopRegularCauchyEnvelope_round_trip y)))

private def bishopRegularCauchyEnvelopeFields :
    BishopRegularCauchyEnvelopeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularCauchyEnvelopeUp.mk W R D S H C P N => [W, R, D, S, H, C, P, N]

private theorem bishopRegularCauchyEnvelope_field_faithful :
    forall x y : BishopRegularCauchyEnvelopeUp,
      bishopRegularCauchyEnvelopeFields x = bishopRegularCauchyEnvelopeFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W R D S H C P N =>
      cases y with
      | mk W' R' D' S' H' C' P' N' =>
          cases hfields
          rfl

instance bishopRegularCauchyEnvelopeBHistCarrier :
    BHistCarrier BishopRegularCauchyEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularCauchyEnvelopeToEventFlow
  fromEventFlow := bishopRegularCauchyEnvelopeFromEventFlow

instance bishopRegularCauchyEnvelopeChapterTasteGate :
    ChapterTasteGate BishopRegularCauchyEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRegularCauchyEnvelopeFromEventFlow
        (bishopRegularCauchyEnvelopeToEventFlow x) = some x
    exact bishopRegularCauchyEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRegularCauchyEnvelopeToEventFlow_injective heq)

instance bishopRegularCauchyEnvelopeFieldFaithful :
    FieldFaithful BishopRegularCauchyEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRegularCauchyEnvelopeFields
  field_faithful := bishopRegularCauchyEnvelope_field_faithful

instance bishopRegularCauchyEnvelopeNontrivial :
    Nontrivial BishopRegularCauchyEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRegularCauchyEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRegularCauchyEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopRegularCauchyEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRegularCauchyEnvelopeChapterTasteGate

theorem BishopRegularCauchyEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopRegularCauchyEnvelopeUp) ∧
      Nonempty (FieldFaithful BishopRegularCauchyEnvelopeUp) ∧
        Nonempty (Nontrivial BishopRegularCauchyEnvelopeUp) ∧
          (∀ h : BHist,
            bishopRegularCauchyEnvelopeDecodeBHist
              (bishopRegularCauchyEnvelopeEncodeBHist h) = h) ∧
            bishopRegularCauchyEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨bishopRegularCauchyEnvelopeChapterTasteGate⟩,
      ⟨bishopRegularCauchyEnvelopeFieldFaithful⟩,
      ⟨bishopRegularCauchyEnvelopeNontrivial⟩,
      bishopRegularCauchyEnvelope_decode_encode_bhist, rfl⟩

end BEDC.Derived.BishopRegularCauchyEnvelopeUp.TasteGate
