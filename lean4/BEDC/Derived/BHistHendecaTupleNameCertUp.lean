import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistHendecaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistHendecaTupleNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L : BHist) :
      BHistHendecaTupleNameCertUp
  deriving DecidableEq

def bHistHendecaTupleNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistHendecaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistHendecaTupleNameCertEncodeBHist h

def bHistHendecaTupleNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistHendecaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistHendecaTupleNameCertDecodeBHist tail)

private theorem BHistHendecaTupleNameCertCarrierAdmission_decode :
    forall h : BHist, bHistHendecaTupleNameCertDecodeBHist
      (bHistHendecaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistHendecaTupleNameCertFields : BHistHendecaTupleNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHendecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, H, C, P, L]

def bHistHendecaTupleNameCertToEventFlow : BHistHendecaTupleNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHendecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L =>
      [[BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R0,
        [BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R7,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R8,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R9,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist R10,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistHendecaTupleNameCertEncodeBHist L]

private def bHistHendecaTupleNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L : RawEvent) :
    BHistHendecaTupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistHendecaTupleNameCertUp.mk
    (bHistHendecaTupleNameCertDecodeBHist R0)
    (bHistHendecaTupleNameCertDecodeBHist R1)
    (bHistHendecaTupleNameCertDecodeBHist R2)
    (bHistHendecaTupleNameCertDecodeBHist R3)
    (bHistHendecaTupleNameCertDecodeBHist R4)
    (bHistHendecaTupleNameCertDecodeBHist R5)
    (bHistHendecaTupleNameCertDecodeBHist R6)
    (bHistHendecaTupleNameCertDecodeBHist R7)
    (bHistHendecaTupleNameCertDecodeBHist R8)
    (bHistHendecaTupleNameCertDecodeBHist R9)
    (bHistHendecaTupleNameCertDecodeBHist R10)
    (bHistHendecaTupleNameCertDecodeBHist H)
    (bHistHendecaTupleNameCertDecodeBHist C)
    (bHistHendecaTupleNameCertDecodeBHist P)
    (bHistHendecaTupleNameCertDecodeBHist L)

def bHistHendecaTupleNameCertFromEventFlow : EventFlow -> Option BHistHendecaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, R0, _tag1, R1, _tag2, R2, _tag3, R3, _tag4, R4, _tag5, R5, _tag6, R6,
      _tag7, R7, _tag8, R8, _tag9, R9, _tag10, R10, _tag11, H, _tag12, C, _tag13,
      P, _tag14, L] =>
      some (bHistHendecaTupleNameCertDecodePacket R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
        H C P L)
  | _ => none

private theorem BHistHendecaTupleNameCertCarrierAdmission_round_trip :
    forall x : BHistHendecaTupleNameCertUp,
      bHistHendecaTupleNameCertFromEventFlow
        (bHistHendecaTupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L =>
      change
        some
          (bHistHendecaTupleNameCertDecodePacket
            (bHistHendecaTupleNameCertEncodeBHist R0)
            (bHistHendecaTupleNameCertEncodeBHist R1)
            (bHistHendecaTupleNameCertEncodeBHist R2)
            (bHistHendecaTupleNameCertEncodeBHist R3)
            (bHistHendecaTupleNameCertEncodeBHist R4)
            (bHistHendecaTupleNameCertEncodeBHist R5)
            (bHistHendecaTupleNameCertEncodeBHist R6)
            (bHistHendecaTupleNameCertEncodeBHist R7)
            (bHistHendecaTupleNameCertEncodeBHist R8)
            (bHistHendecaTupleNameCertEncodeBHist R9)
            (bHistHendecaTupleNameCertEncodeBHist R10)
            (bHistHendecaTupleNameCertEncodeBHist H)
            (bHistHendecaTupleNameCertEncodeBHist C)
            (bHistHendecaTupleNameCertEncodeBHist P)
            (bHistHendecaTupleNameCertEncodeBHist L)) =
          some (BHistHendecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
            H C P L)
      unfold bHistHendecaTupleNameCertDecodePacket
      rw [BHistHendecaTupleNameCertCarrierAdmission_decode R0,
        BHistHendecaTupleNameCertCarrierAdmission_decode R1,
        BHistHendecaTupleNameCertCarrierAdmission_decode R2,
        BHistHendecaTupleNameCertCarrierAdmission_decode R3,
        BHistHendecaTupleNameCertCarrierAdmission_decode R4,
        BHistHendecaTupleNameCertCarrierAdmission_decode R5,
        BHistHendecaTupleNameCertCarrierAdmission_decode R6,
        BHistHendecaTupleNameCertCarrierAdmission_decode R7,
        BHistHendecaTupleNameCertCarrierAdmission_decode R8,
        BHistHendecaTupleNameCertCarrierAdmission_decode R9,
        BHistHendecaTupleNameCertCarrierAdmission_decode R10,
        BHistHendecaTupleNameCertCarrierAdmission_decode H,
        BHistHendecaTupleNameCertCarrierAdmission_decode C,
        BHistHendecaTupleNameCertCarrierAdmission_decode P,
        BHistHendecaTupleNameCertCarrierAdmission_decode L]

private theorem BHistHendecaTupleNameCertCarrierAdmission_injective
    {x y : BHistHendecaTupleNameCertUp} :
    bHistHendecaTupleNameCertToEventFlow x =
        bHistHendecaTupleNameCertToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistHendecaTupleNameCertFromEventFlow
          (bHistHendecaTupleNameCertToEventFlow x) =
        bHistHendecaTupleNameCertFromEventFlow
          (bHistHendecaTupleNameCertToEventFlow y) :=
    congrArg bHistHendecaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistHendecaTupleNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistHendecaTupleNameCertCarrierAdmission_round_trip y)))

private theorem BHistHendecaTupleNameCertCarrierAdmission_field_faithful :
    forall x y : BHistHendecaTupleNameCertUp,
      bHistHendecaTupleNameCertFields x = bHistHendecaTupleNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 H1 C1 P1 L1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bHistHendecaTupleNameCertBHistCarrier :
    BHistCarrier BHistHendecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistHendecaTupleNameCertToEventFlow
  fromEventFlow := bHistHendecaTupleNameCertFromEventFlow

instance bHistHendecaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistHendecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistHendecaTupleNameCertFromEventFlow
          (bHistHendecaTupleNameCertToEventFlow x) = some x
    exact BHistHendecaTupleNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistHendecaTupleNameCertCarrierAdmission_injective heq)

instance bHistHendecaTupleNameCertFieldFaithful :
    FieldFaithful BHistHendecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistHendecaTupleNameCertFields
  field_faithful := BHistHendecaTupleNameCertCarrierAdmission_field_faithful

theorem BHistHendecaTupleNameCertCarrierAdmission
    {R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L : BHist} :
    bHistHendecaTupleNameCertFields
        (BHistHendecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L) =
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, H, C, P, L] ∧
        bHistHendecaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.BHistHendecaTupleNameCertUp
