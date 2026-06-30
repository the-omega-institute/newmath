import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PixleyRoySpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PixleyRoySpaceUp : Type where
  | mk (T S F O W H C Q N : BHist) : PixleyRoySpaceUp
  deriving DecidableEq

def pixleyRoySpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pixleyRoySpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pixleyRoySpaceEncodeBHist h

def pixleyRoySpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pixleyRoySpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pixleyRoySpaceDecodeBHist tail)

private theorem pixleyRoySpace_decode_encode_bhist :
    forall h : BHist, pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pixleyRoySpaceFields : PixleyRoySpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PixleyRoySpaceUp.mk T S F O W H C Q N => [T, S, F, O, W, H, C, Q, N]

def pixleyRoySpaceToEventFlow : PixleyRoySpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PixleyRoySpaceUp.mk T S F O W H C Q N =>
      [[BMark.b0],
        pixleyRoySpaceEncodeBHist T,
        [BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        pixleyRoySpaceEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        pixleyRoySpaceEncodeBHist N]

def pixleyRoySpaceFromEventFlow : EventFlow -> Option PixleyRoySpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | O :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | W :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | Q :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (PixleyRoySpaceUp.mk
                                                                                  (pixleyRoySpaceDecodeBHist T)
                                                                                  (pixleyRoySpaceDecodeBHist S)
                                                                                  (pixleyRoySpaceDecodeBHist F)
                                                                                  (pixleyRoySpaceDecodeBHist O)
                                                                                  (pixleyRoySpaceDecodeBHist W)
                                                                                  (pixleyRoySpaceDecodeBHist H)
                                                                                  (pixleyRoySpaceDecodeBHist C)
                                                                                  (pixleyRoySpaceDecodeBHist Q)
                                                                                  (pixleyRoySpaceDecodeBHist N))
                                                                          | _ :: _ => none

private theorem pixleyRoySpace_round_trip :
    forall x : PixleyRoySpaceUp,
      pixleyRoySpaceFromEventFlow (pixleyRoySpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S F O W H C Q N =>
      change
        some
          (PixleyRoySpaceUp.mk
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist T))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist S))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist F))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist O))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist W))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist H))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist C))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist Q))
            (pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist N))) =
          some (PixleyRoySpaceUp.mk T S F O W H C Q N)
      rw [pixleyRoySpace_decode_encode_bhist T, pixleyRoySpace_decode_encode_bhist S,
        pixleyRoySpace_decode_encode_bhist F, pixleyRoySpace_decode_encode_bhist O,
        pixleyRoySpace_decode_encode_bhist W, pixleyRoySpace_decode_encode_bhist H,
        pixleyRoySpace_decode_encode_bhist C, pixleyRoySpace_decode_encode_bhist Q,
        pixleyRoySpace_decode_encode_bhist N]

private theorem pixleyRoySpaceToEventFlow_injective {x y : PixleyRoySpaceUp} :
    pixleyRoySpaceToEventFlow x = pixleyRoySpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pixleyRoySpaceFromEventFlow (pixleyRoySpaceToEventFlow x) =
        pixleyRoySpaceFromEventFlow (pixleyRoySpaceToEventFlow y) :=
    congrArg pixleyRoySpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pixleyRoySpace_round_trip x).symm
      (Eq.trans hread (pixleyRoySpace_round_trip y)))

private theorem pixleyRoySpace_field_faithful :
    forall x y : PixleyRoySpaceUp, pixleyRoySpaceFields x = pixleyRoySpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance pixleyRoySpaceBHistCarrier : BHistCarrier PixleyRoySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pixleyRoySpaceToEventFlow
  fromEventFlow := pixleyRoySpaceFromEventFlow

instance pixleyRoySpaceChapterTasteGate : ChapterTasteGate PixleyRoySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pixleyRoySpaceFromEventFlow (pixleyRoySpaceToEventFlow x) = some x
    exact pixleyRoySpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pixleyRoySpaceToEventFlow_injective heq)

instance pixleyRoySpaceFieldFaithful : FieldFaithful PixleyRoySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pixleyRoySpaceFields
  field_faithful := pixleyRoySpace_field_faithful

instance pixleyRoySpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PixleyRoySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PixleyRoySpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PixleyRoySpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PixleyRoySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pixleyRoySpaceChapterTasteGate

theorem PixleyRoySpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PixleyRoySpaceUp) ∧
      Nonempty (FieldFaithful PixleyRoySpaceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PixleyRoySpaceUp) ∧
      pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist BHist.Empty) = BHist.Empty ∧
      (∀ h : BHist, pixleyRoySpaceDecodeBHist (pixleyRoySpaceEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨pixleyRoySpaceChapterTasteGate⟩,
      ⟨pixleyRoySpaceFieldFaithful⟩,
      ⟨pixleyRoySpaceNontrivial⟩,
      rfl,
      pixleyRoySpace_decode_encode_bhist⟩

end BEDC.Derived.PixleyRoySpaceUp
