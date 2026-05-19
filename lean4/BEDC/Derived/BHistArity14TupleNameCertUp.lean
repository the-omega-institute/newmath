import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity14TupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity14TupleNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 H C P L : BHist) :
      BHistArity14TupleNameCertUp
  deriving DecidableEq

def bHistArity14TupleNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity14TupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity14TupleNameCertEncodeBHist h

def bHistArity14TupleNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity14TupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity14TupleNameCertDecodeBHist tail)

private theorem bHistArity14TupleNameCert_decode_encode_bhist :
    ∀ h : BHist,
      bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistArity14TupleNameCertFields : BHistArity14TupleNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity14TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13
      H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, H, C, P, L]

def bHistArity14TupleNameCertToEventFlow :
    BHistArity14TupleNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity14TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13
      H C P L =>
      [[BMark.b0], bHistArity14TupleNameCertEncodeBHist R0,
        [BMark.b1, BMark.b0], bHistArity14TupleNameCertEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0], bHistArity14TupleNameCertEncodeBHist R2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0], bHistArity14TupleNameCertEncodeBHist R7,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0], bHistArity14TupleNameCertEncodeBHist R8,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0], bHistArity14TupleNameCertEncodeBHist R9,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R10,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R11,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R12,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist R13,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0], bHistArity14TupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0], bHistArity14TupleNameCertEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0], bHistArity14TupleNameCertEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          bHistArity14TupleNameCertEncodeBHist L]

private def bHistArity14TupleNameCertEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bHistArity14TupleNameCertEventAtDefault index rest

def bHistArity14TupleNameCertFromEventFlow
    (ef : EventFlow) : Option BHistArity14TupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BHistArity14TupleNameCertUp.mk
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 1 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 3 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 5 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 7 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 9 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 11 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 13 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 15 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 17 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 19 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 21 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 23 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 25 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 27 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 29 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 31 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 33 ef))
      (bHistArity14TupleNameCertDecodeBHist
        (bHistArity14TupleNameCertEventAtDefault 35 ef)))

private theorem bHistArity14TupleNameCert_round_trip :
    ∀ x : BHistArity14TupleNameCertUp,
      bHistArity14TupleNameCertFromEventFlow
        (bHistArity14TupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 H C P L =>
      change
        some
          (BHistArity14TupleNameCertUp.mk
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R0))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R1))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R2))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R3))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R4))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R5))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R6))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R7))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R8))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R9))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R10))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R11))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R12))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist R13))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist H))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist C))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist P))
            (bHistArity14TupleNameCertDecodeBHist
              (bHistArity14TupleNameCertEncodeBHist L))) =
          some
            (BHistArity14TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
              R11 R12 R13 H C P L)
      rw [bHistArity14TupleNameCert_decode_encode_bhist R0,
        bHistArity14TupleNameCert_decode_encode_bhist R1,
        bHistArity14TupleNameCert_decode_encode_bhist R2,
        bHistArity14TupleNameCert_decode_encode_bhist R3,
        bHistArity14TupleNameCert_decode_encode_bhist R4,
        bHistArity14TupleNameCert_decode_encode_bhist R5,
        bHistArity14TupleNameCert_decode_encode_bhist R6,
        bHistArity14TupleNameCert_decode_encode_bhist R7,
        bHistArity14TupleNameCert_decode_encode_bhist R8,
        bHistArity14TupleNameCert_decode_encode_bhist R9,
        bHistArity14TupleNameCert_decode_encode_bhist R10,
        bHistArity14TupleNameCert_decode_encode_bhist R11,
        bHistArity14TupleNameCert_decode_encode_bhist R12,
        bHistArity14TupleNameCert_decode_encode_bhist R13,
        bHistArity14TupleNameCert_decode_encode_bhist H,
        bHistArity14TupleNameCert_decode_encode_bhist C,
        bHistArity14TupleNameCert_decode_encode_bhist P,
        bHistArity14TupleNameCert_decode_encode_bhist L]

private theorem bHistArity14TupleNameCertToEventFlow_injective
    {x y : BHistArity14TupleNameCertUp} :
    bHistArity14TupleNameCertToEventFlow x =
      bHistArity14TupleNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistArity14TupleNameCertFromEventFlow
          (bHistArity14TupleNameCertToEventFlow x) =
        bHistArity14TupleNameCertFromEventFlow
          (bHistArity14TupleNameCertToEventFlow y) :=
    congrArg bHistArity14TupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistArity14TupleNameCert_round_trip x).symm
      (Eq.trans hread (bHistArity14TupleNameCert_round_trip y)))

private theorem bHistArity14TupleNameCert_fields_faithful :
    ∀ x y : BHistArity14TupleNameCertUp,
      bHistArity14TupleNameCertFields x =
        bHistArity14TupleNameCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R0₁ R1₁ R2₁ R3₁ R4₁ R5₁ R6₁ R7₁ R8₁ R9₁ R10₁ R11₁ R12₁ R13₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk R0₂ R1₂ R2₂ R3₂ R4₂ R5₂ R6₂ R7₂ R8₂ R9₂ R10₂ R11₂ R12₂ R13₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance bHistArity14TupleNameCertBHistCarrier :
    BHistCarrier BHistArity14TupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity14TupleNameCertToEventFlow
  fromEventFlow := bHistArity14TupleNameCertFromEventFlow

instance bHistArity14TupleNameCertChapterTasteGate :
    ChapterTasteGate BHistArity14TupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity14TupleNameCertFromEventFlow
        (bHistArity14TupleNameCertToEventFlow x) = some x
    exact bHistArity14TupleNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistArity14TupleNameCertToEventFlow_injective heq)

instance bHistArity14TupleNameCertFieldFaithful :
    FieldFaithful BHistArity14TupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistArity14TupleNameCertFields
  field_faithful := bHistArity14TupleNameCert_fields_faithful

def taste_gate : ChapterTasteGate BHistArity14TupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistArity14TupleNameCertChapterTasteGate

theorem BHistArity14TupleNameCertCarrierAdmission
    {R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 H C P L : BHist} :
    bHistArity14TupleNameCertFields
        (BHistArity14TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13
          H C P L) =
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, H, C, P, L] ∧
        bHistArity14TupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨rfl, rfl⟩

end BEDC.Derived.BHistArity14TupleNameCertUp
