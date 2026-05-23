import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity14SequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity14SequenceNameCertUp : Type where
  | mk
      (row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 index
        transport replay provenance localName : BHist) :
      BHistArity14SequenceNameCertUp
  deriving DecidableEq

def bHistArity14SequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity14SequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity14SequenceNameCertEncodeBHist h

def bHistArity14SequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity14SequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity14SequenceNameCertDecodeBHist tail)

private theorem bHistArity14SequenceNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistArity14SequenceNameCertFields :
    BHistArity14SequenceNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity14SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      row10 row11 row12 row13 index transport replay provenance localName =>
      [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12,
        row13, index, transport, replay, provenance, localName]

def bHistArity14SequenceNameCertToEventFlow :
    BHistArity14SequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity14SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      row10 row11 row12 row13 index transport replay provenance localName =>
      [[BMark.b0], bHistArity14SequenceNameCertEncodeBHist row0,
        [BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row1,
        [BMark.b1, BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0], bHistArity14SequenceNameCertEncodeBHist row7,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row8,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row9,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row10,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row11,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row12,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist row13,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0], bHistArity14SequenceNameCertEncodeBHist index,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14SequenceNameCertEncodeBHist localName]

private def bHistArity14SequenceNameCertEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bHistArity14SequenceNameCertEventAtDefault index rest

def bHistArity14SequenceNameCertFromEventFlow
    (ef : EventFlow) : Option BHistArity14SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BHistArity14SequenceNameCertUp.mk
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 1 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 3 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 5 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 7 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 9 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 11 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 13 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 15 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 17 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 19 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 21 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 23 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 25 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 27 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 29 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 31 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 33 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 35 ef))
      (bHistArity14SequenceNameCertDecodeBHist
        (bHistArity14SequenceNameCertEventAtDefault 37 ef)))

private theorem bHistArity14SequenceNameCert_round_trip :
    ∀ x : BHistArity14SequenceNameCertUp,
      bHistArity14SequenceNameCertFromEventFlow
        (bHistArity14SequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 index
      transport replay provenance localName =>
      change
        some
          (BHistArity14SequenceNameCertUp.mk
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row0))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row1))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row2))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row3))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row4))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row5))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row6))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row7))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row8))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row9))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row10))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row11))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row12))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist row13))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist index))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist transport))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist replay))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist provenance))
            (bHistArity14SequenceNameCertDecodeBHist
              (bHistArity14SequenceNameCertEncodeBHist localName))) =
          some
            (BHistArity14SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7
              row8 row9 row10 row11 row12 row13 index transport replay provenance localName)
      rw [bHistArity14SequenceNameCertDecode_encode_bhist row0,
        bHistArity14SequenceNameCertDecode_encode_bhist row1,
        bHistArity14SequenceNameCertDecode_encode_bhist row2,
        bHistArity14SequenceNameCertDecode_encode_bhist row3,
        bHistArity14SequenceNameCertDecode_encode_bhist row4,
        bHistArity14SequenceNameCertDecode_encode_bhist row5,
        bHistArity14SequenceNameCertDecode_encode_bhist row6,
        bHistArity14SequenceNameCertDecode_encode_bhist row7,
        bHistArity14SequenceNameCertDecode_encode_bhist row8,
        bHistArity14SequenceNameCertDecode_encode_bhist row9,
        bHistArity14SequenceNameCertDecode_encode_bhist row10,
        bHistArity14SequenceNameCertDecode_encode_bhist row11,
        bHistArity14SequenceNameCertDecode_encode_bhist row12,
        bHistArity14SequenceNameCertDecode_encode_bhist row13,
        bHistArity14SequenceNameCertDecode_encode_bhist index,
        bHistArity14SequenceNameCertDecode_encode_bhist transport,
        bHistArity14SequenceNameCertDecode_encode_bhist replay,
        bHistArity14SequenceNameCertDecode_encode_bhist provenance,
        bHistArity14SequenceNameCertDecode_encode_bhist localName]

private theorem bHistArity14SequenceNameCertToEventFlow_injective
    {x y : BHistArity14SequenceNameCertUp} :
    bHistArity14SequenceNameCertToEventFlow x =
      bHistArity14SequenceNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistArity14SequenceNameCertFromEventFlow
          (bHistArity14SequenceNameCertToEventFlow x) =
        bHistArity14SequenceNameCertFromEventFlow
          (bHistArity14SequenceNameCertToEventFlow y) :=
    congrArg bHistArity14SequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistArity14SequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistArity14SequenceNameCert_round_trip y)))

private theorem bHistArity14SequenceNameCert_fields_faithful :
    ∀ x y : BHistArity14SequenceNameCertUp,
      bHistArity14SequenceNameCertFields x =
        bHistArity14SequenceNameCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk row0₁ row1₁ row2₁ row3₁ row4₁ row5₁ row6₁ row7₁ row8₁ row9₁ row10₁ row11₁
      row12₁ row13₁ index₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk row0₂ row1₂ row2₂ row3₂ row4₂ row5₂ row6₂ row7₂ row8₂ row9₂ row10₂
          row11₂ row12₂ row13₂ index₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance bHistArity14SequenceNameCertBHistCarrier :
    BHistCarrier BHistArity14SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity14SequenceNameCertToEventFlow
  fromEventFlow := bHistArity14SequenceNameCertFromEventFlow

instance bHistArity14SequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistArity14SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity14SequenceNameCertFromEventFlow
        (bHistArity14SequenceNameCertToEventFlow x) = some x
    exact bHistArity14SequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistArity14SequenceNameCertToEventFlow_injective heq)

instance bHistArity14SequenceNameCertFieldFaithful :
    FieldFaithful BHistArity14SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistArity14SequenceNameCertFields
  field_faithful := bHistArity14SequenceNameCert_fields_faithful

instance bHistArity14SequenceNameCertNontrivial :
    Nontrivial BHistArity14SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistArity14SequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BHistArity14SequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BHistArity14SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistArity14SequenceNameCertChapterTasteGate

theorem BHistArity14SequenceNameCertCarrierAdmission
    (x : BHistArity14SequenceNameCertUp) :
    ∃ row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 index
        transport replay provenance localName : BHist,
      x =
          BHistArity14SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7
            row8 row9 row10 row11 row12 row13 index transport replay provenance localName ∧
        bHistArity14SequenceNameCertToEventFlow x =
          [[BMark.b0], bHistArity14SequenceNameCertEncodeBHist row0,
            [BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row1,
            [BMark.b1, BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row2,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row3,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row4,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row5,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row6,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0], bHistArity14SequenceNameCertEncodeBHist row7,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row8,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist row9,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row10,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row11,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row12,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist row13,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0], bHistArity14SequenceNameCertEncodeBHist index,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist transport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0], bHistArity14SequenceNameCertEncodeBHist replay,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist provenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bHistArity14SequenceNameCertEncodeBHist localName] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 index
      transport replay provenance localName =>
      exact
        ⟨row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11,
          row12, row13, index, transport, replay, provenance, localName, rfl, rfl⟩

theorem BHistArity14SequenceNameCertClassifier_exactness
    {x y : BHistArity14SequenceNameCertUp} :
    bHistArity14SequenceNameCertFields x = bHistArity14SequenceNameCertFields y →
      BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y ∧ x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  have hxy : x = y :=
    bHistArity14SequenceNameCert_fields_faithful x y hfields
  cases hxy
  exact And.intro rfl rfl

end BEDC.Derived.BHistArity14SequenceNameCertUp
