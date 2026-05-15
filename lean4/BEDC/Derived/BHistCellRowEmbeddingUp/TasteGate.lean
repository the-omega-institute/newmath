import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistCellRowEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistCellRowEmbeddingUp : Type where
  | mk (source bitRow width orbitZero readback transports routes provenance name : BHist) :
      BHistCellRowEmbeddingUp
  deriving DecidableEq

def bhistCellRowEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bhistCellRowEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bhistCellRowEmbeddingEncodeBHist h

def bhistCellRowEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bhistCellRowEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bhistCellRowEmbeddingDecodeBHist tail)

private theorem bhistCellRowEmbeddingDecode_encode_bhist :
    ∀ h : BHist, bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bhistCellRowEmbeddingToEventFlow : BHistCellRowEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistCellRowEmbeddingUp.mk source bitRow width orbitZero readback transports routes
      provenance name =>
      [[BMark.b0],
        bhistCellRowEmbeddingEncodeBHist source,
        [BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist bitRow,
        [BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist width,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist orbitZero,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bhistCellRowEmbeddingEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist name]

def bhistCellRowEmbeddingFromEventFlow : EventFlow → Option BHistCellRowEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | bitRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | width :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | orbitZero :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BHistCellRowEmbeddingUp.mk
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    source)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    bitRow)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    width)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    orbitZero)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    readback)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    transports)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    routes)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    provenance)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem bhistCellRowEmbedding_round_trip :
    ∀ x : BHistCellRowEmbeddingUp,
      bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source bitRow width orbitZero readback transports routes provenance name =>
      change
        some
          (BHistCellRowEmbeddingUp.mk
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist source))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist bitRow))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist width))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist orbitZero))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist readback))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist transports))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist routes))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist provenance))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist name))) =
          some
            (BHistCellRowEmbeddingUp.mk source bitRow width orbitZero readback transports routes
              provenance name)
      rw [bhistCellRowEmbeddingDecode_encode_bhist source,
        bhistCellRowEmbeddingDecode_encode_bhist bitRow,
        bhistCellRowEmbeddingDecode_encode_bhist width,
        bhistCellRowEmbeddingDecode_encode_bhist orbitZero,
        bhistCellRowEmbeddingDecode_encode_bhist readback,
        bhistCellRowEmbeddingDecode_encode_bhist transports,
        bhistCellRowEmbeddingDecode_encode_bhist routes,
        bhistCellRowEmbeddingDecode_encode_bhist provenance,
        bhistCellRowEmbeddingDecode_encode_bhist name]

private theorem bhistCellRowEmbeddingToEventFlow_injective {x y : BHistCellRowEmbeddingUp} :
    bhistCellRowEmbeddingToEventFlow x = bhistCellRowEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) =
        bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow y) :=
    congrArg bhistCellRowEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bhistCellRowEmbedding_round_trip x).symm
      (Eq.trans hread (bhistCellRowEmbedding_round_trip y)))

instance bhistCellRowEmbeddingBHistCarrier : BHistCarrier BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bhistCellRowEmbeddingToEventFlow
  fromEventFlow := bhistCellRowEmbeddingFromEventFlow

instance bhistCellRowEmbeddingChapterTasteGate : ChapterTasteGate BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) = some x
    exact bhistCellRowEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bhistCellRowEmbeddingToEventFlow_injective heq)

instance bhistCellRowEmbeddingFieldFaithful : FieldFaithful BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BHistCellRowEmbeddingUp.mk source bitRow width orbitZero readback transports routes
        provenance name =>
        [source, bitRow, width, orbitZero, readback, transports, routes, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ bitRow₁ width₁ orbitZero₁ readback₁ transports₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk source₂ bitRow₂ width₂ orbitZero₂ readback₂ transports₂ routes₂ provenance₂
            name₂ =>
            simp only [] at h
            cases h
            rfl

instance bhistCellRowEmbeddingNontrivial : Nontrivial BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistCellRowEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistCellRowEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BHistCellRowEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bhistCellRowEmbeddingChapterTasteGate

end BEDC.Derived.BHistCellRowEmbeddingUp
