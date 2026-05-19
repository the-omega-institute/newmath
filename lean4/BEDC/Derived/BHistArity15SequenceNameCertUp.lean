import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity15SequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity15SequenceNameCertUp : Type where
  | mk
      (row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
        index transport replay provenance localName : BHist) :
      BHistArity15SequenceNameCertUp
  deriving DecidableEq

def bHistArity15SequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity15SequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity15SequenceNameCertEncodeBHist h

def bHistArity15SequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity15SequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity15SequenceNameCertDecodeBHist tail)

private theorem bHistArity15SequenceNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistArity15SequenceNameCertFields :
    BHistArity15SequenceNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity15SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      row10 row11 row12 row13 row14 index transport replay provenance localName =>
      [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12,
        row13, row14, index, transport, replay, provenance, localName]

def bHistArity15SequenceNameCertToEventFlow :
    BHistArity15SequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity15SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      row10 row11 row12 row13 row14 index transport replay provenance localName =>
      [[BMark.b0],
        bHistArity15SequenceNameCertEncodeBHist row0,
        bHistArity15SequenceNameCertEncodeBHist row1,
        bHistArity15SequenceNameCertEncodeBHist row2,
        bHistArity15SequenceNameCertEncodeBHist row3,
        bHistArity15SequenceNameCertEncodeBHist row4,
        bHistArity15SequenceNameCertEncodeBHist row5,
        bHistArity15SequenceNameCertEncodeBHist row6,
        bHistArity15SequenceNameCertEncodeBHist row7,
        bHistArity15SequenceNameCertEncodeBHist row8,
        bHistArity15SequenceNameCertEncodeBHist row9,
        bHistArity15SequenceNameCertEncodeBHist row10,
        bHistArity15SequenceNameCertEncodeBHist row11,
        bHistArity15SequenceNameCertEncodeBHist row12,
        bHistArity15SequenceNameCertEncodeBHist row13,
        bHistArity15SequenceNameCertEncodeBHist row14,
        bHistArity15SequenceNameCertEncodeBHist index,
        bHistArity15SequenceNameCertEncodeBHist transport,
        bHistArity15SequenceNameCertEncodeBHist replay,
        bHistArity15SequenceNameCertEncodeBHist provenance,
        bHistArity15SequenceNameCertEncodeBHist localName]

private def bHistArity15SequenceNameCertEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bHistArity15SequenceNameCertEventAtDefault index rest

def bHistArity15SequenceNameCertFromEventFlow
    (ef : EventFlow) : Option BHistArity15SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BHistArity15SequenceNameCertUp.mk
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 1 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 2 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 3 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 4 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 5 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 6 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 7 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 8 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 9 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 10 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 11 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 12 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 13 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 14 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 15 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 16 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 17 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 18 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 19 ef))
      (bHistArity15SequenceNameCertDecodeBHist
        (bHistArity15SequenceNameCertEventAtDefault 20 ef)))

private theorem bHistArity15SequenceNameCert_round_trip :
    ∀ x : BHistArity15SequenceNameCertUp,
      bHistArity15SequenceNameCertFromEventFlow
        (bHistArity15SequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
      index transport replay provenance localName =>
      change
        some
          (BHistArity15SequenceNameCertUp.mk
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row0))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row1))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row2))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row3))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row4))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row5))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row6))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row7))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row8))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row9))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row10))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row11))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row12))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row13))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist row14))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist index))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist transport))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist replay))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist provenance))
            (bHistArity15SequenceNameCertDecodeBHist
              (bHistArity15SequenceNameCertEncodeBHist localName))) =
          some
            (BHistArity15SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7
              row8 row9 row10 row11 row12 row13 row14 index transport replay provenance
              localName)
      rw [bHistArity15SequenceNameCertDecode_encode_bhist row0,
        bHistArity15SequenceNameCertDecode_encode_bhist row1,
        bHistArity15SequenceNameCertDecode_encode_bhist row2,
        bHistArity15SequenceNameCertDecode_encode_bhist row3,
        bHistArity15SequenceNameCertDecode_encode_bhist row4,
        bHistArity15SequenceNameCertDecode_encode_bhist row5,
        bHistArity15SequenceNameCertDecode_encode_bhist row6,
        bHistArity15SequenceNameCertDecode_encode_bhist row7,
        bHistArity15SequenceNameCertDecode_encode_bhist row8,
        bHistArity15SequenceNameCertDecode_encode_bhist row9,
        bHistArity15SequenceNameCertDecode_encode_bhist row10,
        bHistArity15SequenceNameCertDecode_encode_bhist row11,
        bHistArity15SequenceNameCertDecode_encode_bhist row12,
        bHistArity15SequenceNameCertDecode_encode_bhist row13,
        bHistArity15SequenceNameCertDecode_encode_bhist row14,
        bHistArity15SequenceNameCertDecode_encode_bhist index,
        bHistArity15SequenceNameCertDecode_encode_bhist transport,
        bHistArity15SequenceNameCertDecode_encode_bhist replay,
        bHistArity15SequenceNameCertDecode_encode_bhist provenance,
        bHistArity15SequenceNameCertDecode_encode_bhist localName]

private theorem bHistArity15SequenceNameCertToEventFlow_injective
    {x y : BHistArity15SequenceNameCertUp} :
    bHistArity15SequenceNameCertToEventFlow x =
      bHistArity15SequenceNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistArity15SequenceNameCertFromEventFlow
          (bHistArity15SequenceNameCertToEventFlow x) =
        bHistArity15SequenceNameCertFromEventFlow
          (bHistArity15SequenceNameCertToEventFlow y) :=
    congrArg bHistArity15SequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistArity15SequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistArity15SequenceNameCert_round_trip y)))

private theorem bHistArity15SequenceNameCert_fields_faithful :
    ∀ x y : BHistArity15SequenceNameCertUp,
      bHistArity15SequenceNameCertFields x =
        bHistArity15SequenceNameCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk row0₁ row1₁ row2₁ row3₁ row4₁ row5₁ row6₁ row7₁ row8₁ row9₁ row10₁ row11₁
      row12₁ row13₁ row14₁ index₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk row0₂ row1₂ row2₂ row3₂ row4₂ row5₂ row6₂ row7₂ row8₂ row9₂ row10₂
          row11₂ row12₂ row13₂ row14₂ index₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance bHistArity15SequenceNameCertBHistCarrier :
    BHistCarrier BHistArity15SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity15SequenceNameCertToEventFlow
  fromEventFlow := bHistArity15SequenceNameCertFromEventFlow

instance bHistArity15SequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistArity15SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity15SequenceNameCertFromEventFlow
        (bHistArity15SequenceNameCertToEventFlow x) = some x
    exact bHistArity15SequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistArity15SequenceNameCertToEventFlow_injective heq)

instance bHistArity15SequenceNameCertFieldFaithful :
    FieldFaithful BHistArity15SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistArity15SequenceNameCertFields
  field_faithful := bHistArity15SequenceNameCert_fields_faithful

instance bHistArity15SequenceNameCertNontrivial :
    Nontrivial BHistArity15SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistArity15SequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BHistArity15SequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BHistArity15SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistArity15SequenceNameCertChapterTasteGate

theorem BHistArity15SequenceNameCertCarrierAdmission
    (x : BHistArity15SequenceNameCertUp) :
    ∃ row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
        index transport replay provenance localName : BHist,
      x =
          BHistArity15SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7
            row8 row9 row10 row11 row12 row13 row14 index transport replay provenance
            localName ∧
        bHistArity15SequenceNameCertFields x =
          [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11,
            row12, row13, row14, index, transport, replay, provenance, localName] ∧
          List.Mem [BMark.b0] (bHistArity15SequenceNameCertToEventFlow x) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
      index transport replay provenance localName =>
      exact
        ⟨row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11,
          row12, row13, row14, index, transport, replay, provenance, localName, rfl, rfl,
          List.Mem.head _⟩

end BEDC.Derived.BHistArity15SequenceNameCertUp
