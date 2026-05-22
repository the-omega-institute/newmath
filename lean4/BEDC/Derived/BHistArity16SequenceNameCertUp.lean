import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity16SequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity16SequenceNameCertUp : Type where
  | mk
      (row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
        row15 index transport replay provenance localName : BHist) :
      BHistArity16SequenceNameCertUp
  deriving DecidableEq

def bHistArity16SequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity16SequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity16SequenceNameCertEncodeBHist h

def bHistArity16SequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity16SequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity16SequenceNameCertDecodeBHist tail)

private theorem BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bHistArity16SequenceNameCertDecodeBHist
        (bHistArity16SequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistArity16SequenceNameCertFields :
    BHistArity16SequenceNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity16SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      row10 row11 row12 row13 row14 row15 index transport replay provenance localName =>
      [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11,
        row12, row13, row14, row15, index, transport, replay, provenance, localName]

def bHistArity16SequenceNameCertToEventFlow :
    BHistArity16SequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity16SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      row10 row11 row12 row13 row14 row15 index transport replay provenance localName =>
      [[BMark.b1, BMark.b0, BMark.b0, BMark.b1],
        bHistArity16SequenceNameCertEncodeBHist row0,
        bHistArity16SequenceNameCertEncodeBHist row1,
        bHistArity16SequenceNameCertEncodeBHist row2,
        bHistArity16SequenceNameCertEncodeBHist row3,
        bHistArity16SequenceNameCertEncodeBHist row4,
        bHistArity16SequenceNameCertEncodeBHist row5,
        bHistArity16SequenceNameCertEncodeBHist row6,
        bHistArity16SequenceNameCertEncodeBHist row7,
        bHistArity16SequenceNameCertEncodeBHist row8,
        bHistArity16SequenceNameCertEncodeBHist row9,
        bHistArity16SequenceNameCertEncodeBHist row10,
        bHistArity16SequenceNameCertEncodeBHist row11,
        bHistArity16SequenceNameCertEncodeBHist row12,
        bHistArity16SequenceNameCertEncodeBHist row13,
        bHistArity16SequenceNameCertEncodeBHist row14,
        bHistArity16SequenceNameCertEncodeBHist row15,
        bHistArity16SequenceNameCertEncodeBHist index,
        bHistArity16SequenceNameCertEncodeBHist transport,
        bHistArity16SequenceNameCertEncodeBHist replay,
        bHistArity16SequenceNameCertEncodeBHist provenance,
        bHistArity16SequenceNameCertEncodeBHist localName]

private def BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault index rest

def bHistArity16SequenceNameCertFromEventFlow
    (ef : EventFlow) : Option BHistArity16SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BHistArity16SequenceNameCertUp.mk
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 12 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 14 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 16 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 17 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 18 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 19 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 20 ef))
      (bHistArity16SequenceNameCertDecodeBHist
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_eventAtDefault 21 ef)))

private theorem BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BHistArity16SequenceNameCertUp,
      bHistArity16SequenceNameCertFromEventFlow
        (bHistArity16SequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
      row15 index transport replay provenance localName =>
      change
        some
          (BHistArity16SequenceNameCertUp.mk
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row0))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row1))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row2))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row3))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row4))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row5))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row6))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row7))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row8))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row9))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row10))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row11))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row12))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row13))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row14))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist row15))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist index))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist transport))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist replay))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist provenance))
            (bHistArity16SequenceNameCertDecodeBHist
              (bHistArity16SequenceNameCertEncodeBHist localName))) =
          some
            (BHistArity16SequenceNameCertUp.mk row0 row1 row2 row3 row4 row5 row6 row7
              row8 row9 row10 row11 row12 row13 row14 row15 index transport replay
              provenance localName)
      rw [BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row0,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row1,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row2,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row3,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row4,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row5,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row6,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row7,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row8,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row9,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row10,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row11,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row12,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row13,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row14,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode row15,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode index,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode transport,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode replay,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode provenance,
        BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_decode_encode localName]

private theorem BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BHistArity16SequenceNameCertUp} :
    bHistArity16SequenceNameCertToEventFlow x =
      bHistArity16SequenceNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistArity16SequenceNameCertFromEventFlow
          (bHistArity16SequenceNameCertToEventFlow x) =
        bHistArity16SequenceNameCertFromEventFlow
          (bHistArity16SequenceNameCertToEventFlow y) :=
    congrArg bHistArity16SequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_round_trip y)))

private theorem BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BHistArity16SequenceNameCertUp,
      bHistArity16SequenceNameCertFields x =
        bHistArity16SequenceNameCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk row0₁ row1₁ row2₁ row3₁ row4₁ row5₁ row6₁ row7₁ row8₁ row9₁ row10₁ row11₁
      row12₁ row13₁ row14₁ row15₁ index₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk row0₂ row1₂ row2₂ row3₂ row4₂ row5₂ row6₂ row7₂ row8₂ row9₂ row10₂
          row11₂ row12₂ row13₂ row14₂ row15₂ index₂ transport₂ replay₂ provenance₂
          localName₂ =>
          cases hfields
          rfl

instance bHistArity16SequenceNameCertBHistCarrier :
    BHistCarrier BHistArity16SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity16SequenceNameCertToEventFlow
  fromEventFlow := bHistArity16SequenceNameCertFromEventFlow

instance bHistArity16SequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistArity16SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity16SequenceNameCertFromEventFlow
        (bHistArity16SequenceNameCertToEventFlow x) = some x
    exact BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bHistArity16SequenceNameCertFieldFaithful :
    FieldFaithful BHistArity16SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistArity16SequenceNameCertFields
  field_faithful :=
    BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_fields_faithful

instance bHistArity16SequenceNameCertNontrivial :
    Nontrivial BHistArity16SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistArity16SequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BHistArity16SequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BHistArity16SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistArity16SequenceNameCertChapterTasteGate

theorem BHistArity16SequenceNameCertTasteGate_single_carrier_alignment :
    (Nonempty (ChapterTasteGate BHistArity16SequenceNameCertUp)) ∧
      (forall x : BHistArity16SequenceNameCertUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact Nonempty.intro bHistArity16SequenceNameCertChapterTasteGate
  · intro x
    change
      bHistArity16SequenceNameCertFromEventFlow
        (bHistArity16SequenceNameCertToEventFlow x) = some x
    exact BHistArity16SequenceNameCertTasteGate_single_carrier_alignment_round_trip x

end BEDC.Derived.BHistArity16SequenceNameCertUp
