import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistDodecaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistDodecaTupleNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P L : BHist) :
      BHistDodecaTupleNameCertUp
  deriving DecidableEq

def bHistDodecaTupleNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistDodecaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistDodecaTupleNameCertEncodeBHist h

def bHistDodecaTupleNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistDodecaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistDodecaTupleNameCertDecodeBHist tail)

private theorem BHistDodecaTupleNameCertCarrierAdmission_decode :
    forall h : BHist, bHistDodecaTupleNameCertDecodeBHist
      (bHistDodecaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistDodecaTupleNameCertFields : BHistDodecaTupleNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDodecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, H, C, P, L]

def bHistDodecaTupleNameCertToEventFlow : BHistDodecaTupleNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDodecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P L =>
      [[BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist R0,
        [BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist R1,
        [BMark.b0, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist R2,
        [BMark.b0, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist R5,
        [BMark.b0, BMark.b0, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist R6,
        [BMark.b0, BMark.b0, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist R7,
        [BMark.b0, BMark.b1, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist R8,
        [BMark.b0, BMark.b1, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist R9,
        [BMark.b1, BMark.b0, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist R10,
        [BMark.b1, BMark.b0, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist R11,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist C,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0],
        bHistDodecaTupleNameCertEncodeBHist P,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b1],
        bHistDodecaTupleNameCertEncodeBHist L]

private def bHistDodecaTupleNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P L : RawEvent) :
    BHistDodecaTupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistDodecaTupleNameCertUp.mk
    (bHistDodecaTupleNameCertDecodeBHist R0)
    (bHistDodecaTupleNameCertDecodeBHist R1)
    (bHistDodecaTupleNameCertDecodeBHist R2)
    (bHistDodecaTupleNameCertDecodeBHist R3)
    (bHistDodecaTupleNameCertDecodeBHist R4)
    (bHistDodecaTupleNameCertDecodeBHist R5)
    (bHistDodecaTupleNameCertDecodeBHist R6)
    (bHistDodecaTupleNameCertDecodeBHist R7)
    (bHistDodecaTupleNameCertDecodeBHist R8)
    (bHistDodecaTupleNameCertDecodeBHist R9)
    (bHistDodecaTupleNameCertDecodeBHist R10)
    (bHistDodecaTupleNameCertDecodeBHist R11)
    (bHistDodecaTupleNameCertDecodeBHist H)
    (bHistDodecaTupleNameCertDecodeBHist C)
    (bHistDodecaTupleNameCertDecodeBHist P)
    (bHistDodecaTupleNameCertDecodeBHist L)

def bHistDodecaTupleNameCertFromEventFlow : EventFlow -> Option BHistDodecaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, R0, _tag1, R1, _tag2, R2, _tag3, R3, _tag4, R4, _tag5, R5, _tag6, R6,
      _tag7, R7, _tag8, R8, _tag9, R9, _tag10, R10, _tag11, R11, _tag12, H, _tag13,
      C, _tag14, P, _tag15, L] =>
      some (bHistDodecaTupleNameCertDecodePacket R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
        R11 H C P L)
  | _ => none

private theorem BHistDodecaTupleNameCertCarrierAdmission_round_trip :
    forall x : BHistDodecaTupleNameCertUp,
      bHistDodecaTupleNameCertFromEventFlow
        (bHistDodecaTupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P L =>
      change
        some
          (bHistDodecaTupleNameCertDecodePacket
            (bHistDodecaTupleNameCertEncodeBHist R0)
            (bHistDodecaTupleNameCertEncodeBHist R1)
            (bHistDodecaTupleNameCertEncodeBHist R2)
            (bHistDodecaTupleNameCertEncodeBHist R3)
            (bHistDodecaTupleNameCertEncodeBHist R4)
            (bHistDodecaTupleNameCertEncodeBHist R5)
            (bHistDodecaTupleNameCertEncodeBHist R6)
            (bHistDodecaTupleNameCertEncodeBHist R7)
            (bHistDodecaTupleNameCertEncodeBHist R8)
            (bHistDodecaTupleNameCertEncodeBHist R9)
            (bHistDodecaTupleNameCertEncodeBHist R10)
            (bHistDodecaTupleNameCertEncodeBHist R11)
            (bHistDodecaTupleNameCertEncodeBHist H)
            (bHistDodecaTupleNameCertEncodeBHist C)
            (bHistDodecaTupleNameCertEncodeBHist P)
            (bHistDodecaTupleNameCertEncodeBHist L)) =
          some
            (BHistDodecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11
              H C P L)
      unfold bHistDodecaTupleNameCertDecodePacket
      rw [BHistDodecaTupleNameCertCarrierAdmission_decode R0,
        BHistDodecaTupleNameCertCarrierAdmission_decode R1,
        BHistDodecaTupleNameCertCarrierAdmission_decode R2,
        BHistDodecaTupleNameCertCarrierAdmission_decode R3,
        BHistDodecaTupleNameCertCarrierAdmission_decode R4,
        BHistDodecaTupleNameCertCarrierAdmission_decode R5,
        BHistDodecaTupleNameCertCarrierAdmission_decode R6,
        BHistDodecaTupleNameCertCarrierAdmission_decode R7,
        BHistDodecaTupleNameCertCarrierAdmission_decode R8,
        BHistDodecaTupleNameCertCarrierAdmission_decode R9,
        BHistDodecaTupleNameCertCarrierAdmission_decode R10,
        BHistDodecaTupleNameCertCarrierAdmission_decode R11,
        BHistDodecaTupleNameCertCarrierAdmission_decode H,
        BHistDodecaTupleNameCertCarrierAdmission_decode C,
        BHistDodecaTupleNameCertCarrierAdmission_decode P,
        BHistDodecaTupleNameCertCarrierAdmission_decode L]

private theorem BHistDodecaTupleNameCertCarrierAdmission_injective
    {x y : BHistDodecaTupleNameCertUp} :
    bHistDodecaTupleNameCertToEventFlow x =
        bHistDodecaTupleNameCertToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistDodecaTupleNameCertFromEventFlow
          (bHistDodecaTupleNameCertToEventFlow x) =
        bHistDodecaTupleNameCertFromEventFlow
          (bHistDodecaTupleNameCertToEventFlow y) :=
    congrArg bHistDodecaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistDodecaTupleNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistDodecaTupleNameCertCarrierAdmission_round_trip y)))

private theorem BHistDodecaTupleNameCertCarrierAdmission_field_faithful :
    forall x y : BHistDodecaTupleNameCertUp,
      bHistDodecaTupleNameCertFields x = bHistDodecaTupleNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 R111 H1 C1 P1 L1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 R112 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bHistDodecaTupleNameCertBHistCarrier :
    BHistCarrier BHistDodecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistDodecaTupleNameCertToEventFlow
  fromEventFlow := bHistDodecaTupleNameCertFromEventFlow

instance bHistDodecaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistDodecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistDodecaTupleNameCertFromEventFlow
          (bHistDodecaTupleNameCertToEventFlow x) = some x
    exact BHistDodecaTupleNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistDodecaTupleNameCertCarrierAdmission_injective heq)

instance bHistDodecaTupleNameCertFieldFaithful :
    FieldFaithful BHistDodecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistDodecaTupleNameCertFields
  field_faithful := BHistDodecaTupleNameCertCarrierAdmission_field_faithful

theorem BHistDodecaTupleNameCertCarrierAdmission
    {R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P L : BHist} :
    bHistDodecaTupleNameCertFields
        (BHistDodecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11
          H C P L) =
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, H, C, P, L] ∧
        bHistDodecaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.BHistDodecaTupleNameCertUp
