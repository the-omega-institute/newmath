import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistHeptaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistHeptaTupleNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 H C P L : BHist) :
      BHistHeptaTupleNameCertUp
  deriving DecidableEq

def bHistHeptaTupleNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistHeptaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistHeptaTupleNameCertEncodeBHist h

def bHistHeptaTupleNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistHeptaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistHeptaTupleNameCertDecodeBHist tail)

private theorem BHistHeptaTupleNameCertCarrierAdmission_decode :
    forall h : BHist, bHistHeptaTupleNameCertDecodeBHist
      (bHistHeptaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistHeptaTupleNameCertFields : BHistHeptaTupleNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHeptaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, H, C, P, L]

def bHistHeptaTupleNameCertToEventFlow : BHistHeptaTupleNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHeptaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 H C P L =>
      [[BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R0,
        [BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist R6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaTupleNameCertEncodeBHist L]

private def bHistHeptaTupleNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 H C P L : RawEvent) :
    BHistHeptaTupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistHeptaTupleNameCertUp.mk
    (bHistHeptaTupleNameCertDecodeBHist R0)
    (bHistHeptaTupleNameCertDecodeBHist R1)
    (bHistHeptaTupleNameCertDecodeBHist R2)
    (bHistHeptaTupleNameCertDecodeBHist R3)
    (bHistHeptaTupleNameCertDecodeBHist R4)
    (bHistHeptaTupleNameCertDecodeBHist R5)
    (bHistHeptaTupleNameCertDecodeBHist R6)
    (bHistHeptaTupleNameCertDecodeBHist H)
    (bHistHeptaTupleNameCertDecodeBHist C)
    (bHistHeptaTupleNameCertDecodeBHist P)
    (bHistHeptaTupleNameCertDecodeBHist L)

def bHistHeptaTupleNameCertFromEventFlow : EventFlow -> Option BHistHeptaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, R0, _tag1, R1, _tag2, R2, _tag3, R3, _tag4, R4, _tag5, R5, _tag6, R6,
      _tag7, H, _tag8, C, _tag9, P, _tag10, L] =>
      some (bHistHeptaTupleNameCertDecodePacket R0 R1 R2 R3 R4 R5 R6 H C P L)
  | _ => none

private theorem BHistHeptaTupleNameCertCarrierAdmission_round_trip :
    forall x : BHistHeptaTupleNameCertUp,
      bHistHeptaTupleNameCertFromEventFlow (bHistHeptaTupleNameCertToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 H C P L =>
      change
        some
          (bHistHeptaTupleNameCertDecodePacket
            (bHistHeptaTupleNameCertEncodeBHist R0)
            (bHistHeptaTupleNameCertEncodeBHist R1)
            (bHistHeptaTupleNameCertEncodeBHist R2)
            (bHistHeptaTupleNameCertEncodeBHist R3)
            (bHistHeptaTupleNameCertEncodeBHist R4)
            (bHistHeptaTupleNameCertEncodeBHist R5)
            (bHistHeptaTupleNameCertEncodeBHist R6)
            (bHistHeptaTupleNameCertEncodeBHist H)
            (bHistHeptaTupleNameCertEncodeBHist C)
            (bHistHeptaTupleNameCertEncodeBHist P)
            (bHistHeptaTupleNameCertEncodeBHist L)) =
          some (BHistHeptaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 H C P L)
      unfold bHistHeptaTupleNameCertDecodePacket
      rw [BHistHeptaTupleNameCertCarrierAdmission_decode R0,
        BHistHeptaTupleNameCertCarrierAdmission_decode R1,
        BHistHeptaTupleNameCertCarrierAdmission_decode R2,
        BHistHeptaTupleNameCertCarrierAdmission_decode R3,
        BHistHeptaTupleNameCertCarrierAdmission_decode R4,
        BHistHeptaTupleNameCertCarrierAdmission_decode R5,
        BHistHeptaTupleNameCertCarrierAdmission_decode R6,
        BHistHeptaTupleNameCertCarrierAdmission_decode H,
        BHistHeptaTupleNameCertCarrierAdmission_decode C,
        BHistHeptaTupleNameCertCarrierAdmission_decode P,
        BHistHeptaTupleNameCertCarrierAdmission_decode L]

private theorem BHistHeptaTupleNameCertCarrierAdmission_injective
    {x y : BHistHeptaTupleNameCertUp} :
    bHistHeptaTupleNameCertToEventFlow x = bHistHeptaTupleNameCertToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistHeptaTupleNameCertFromEventFlow (bHistHeptaTupleNameCertToEventFlow x) =
        bHistHeptaTupleNameCertFromEventFlow (bHistHeptaTupleNameCertToEventFlow y) :=
    congrArg bHistHeptaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistHeptaTupleNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistHeptaTupleNameCertCarrierAdmission_round_trip y)))

private theorem BHistHeptaTupleNameCertCarrierAdmission_field_faithful :
    forall x y : BHistHeptaTupleNameCertUp,
      bHistHeptaTupleNameCertFields x = bHistHeptaTupleNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 H1 C1 P1 L1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bHistHeptaTupleNameCertBHistCarrier : BHistCarrier BHistHeptaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistHeptaTupleNameCertToEventFlow
  fromEventFlow := bHistHeptaTupleNameCertFromEventFlow

instance bHistHeptaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistHeptaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistHeptaTupleNameCertFromEventFlow (bHistHeptaTupleNameCertToEventFlow x) = some x
    exact BHistHeptaTupleNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistHeptaTupleNameCertCarrierAdmission_injective heq)

instance bHistHeptaTupleNameCertFieldFaithful :
    FieldFaithful BHistHeptaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistHeptaTupleNameCertFields
  field_faithful := BHistHeptaTupleNameCertCarrierAdmission_field_faithful

theorem BHistHeptaTupleNameCertCarrierAdmission
    {R0 R1 R2 R3 R4 R5 R6 H C P L : BHist} :
    bHistHeptaTupleNameCertFields
        (BHistHeptaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 H C P L) =
      [R0, R1, R2, R3, R4, R5, R6, H, C, P, L] ∧
        bHistHeptaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.BHistHeptaTupleNameCertUp
