import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistOctaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistOctaTupleNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 H C P L : BHist) :
      BHistOctaTupleNameCertUp
  deriving DecidableEq

def bHistOctaTupleNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistOctaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistOctaTupleNameCertEncodeBHist h

def bHistOctaTupleNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistOctaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistOctaTupleNameCertDecodeBHist tail)

private theorem BHistOctaTupleNameCertCarrierAdmission_decode :
    forall h : BHist, bHistOctaTupleNameCertDecodeBHist
      (bHistOctaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistOctaTupleNameCertFields : BHistOctaTupleNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistOctaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, R7, H, C, P, L]

def bHistOctaTupleNameCertToEventFlow : BHistOctaTupleNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistOctaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 H C P L =>
      [[BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R0,
        [BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistOctaTupleNameCertEncodeBHist R7,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistOctaTupleNameCertEncodeBHist L]

private def bHistOctaTupleNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 R7 H C P L : RawEvent) :
    BHistOctaTupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistOctaTupleNameCertUp.mk
    (bHistOctaTupleNameCertDecodeBHist R0)
    (bHistOctaTupleNameCertDecodeBHist R1)
    (bHistOctaTupleNameCertDecodeBHist R2)
    (bHistOctaTupleNameCertDecodeBHist R3)
    (bHistOctaTupleNameCertDecodeBHist R4)
    (bHistOctaTupleNameCertDecodeBHist R5)
    (bHistOctaTupleNameCertDecodeBHist R6)
    (bHistOctaTupleNameCertDecodeBHist R7)
    (bHistOctaTupleNameCertDecodeBHist H)
    (bHistOctaTupleNameCertDecodeBHist C)
    (bHistOctaTupleNameCertDecodeBHist P)
    (bHistOctaTupleNameCertDecodeBHist L)

def bHistOctaTupleNameCertFromEventFlow : EventFlow -> Option BHistOctaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, R0, _tag1, R1, _tag2, R2, _tag3, R3, _tag4, R4, _tag5, R5, _tag6, R6,
      _tag7, R7, _tag8, H, _tag9, C, _tag10, P, _tag11, L] =>
      some (bHistOctaTupleNameCertDecodePacket R0 R1 R2 R3 R4 R5 R6 R7 H C P L)
  | _ => none

private theorem BHistOctaTupleNameCertCarrierAdmission_round_trip :
    forall x : BHistOctaTupleNameCertUp,
      bHistOctaTupleNameCertFromEventFlow (bHistOctaTupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 H C P L =>
      change
        some
          (bHistOctaTupleNameCertDecodePacket
            (bHistOctaTupleNameCertEncodeBHist R0)
            (bHistOctaTupleNameCertEncodeBHist R1)
            (bHistOctaTupleNameCertEncodeBHist R2)
            (bHistOctaTupleNameCertEncodeBHist R3)
            (bHistOctaTupleNameCertEncodeBHist R4)
            (bHistOctaTupleNameCertEncodeBHist R5)
            (bHistOctaTupleNameCertEncodeBHist R6)
            (bHistOctaTupleNameCertEncodeBHist R7)
            (bHistOctaTupleNameCertEncodeBHist H)
            (bHistOctaTupleNameCertEncodeBHist C)
            (bHistOctaTupleNameCertEncodeBHist P)
            (bHistOctaTupleNameCertEncodeBHist L)) =
          some (BHistOctaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 H C P L)
      unfold bHistOctaTupleNameCertDecodePacket
      rw [BHistOctaTupleNameCertCarrierAdmission_decode R0,
        BHistOctaTupleNameCertCarrierAdmission_decode R1,
        BHistOctaTupleNameCertCarrierAdmission_decode R2,
        BHistOctaTupleNameCertCarrierAdmission_decode R3,
        BHistOctaTupleNameCertCarrierAdmission_decode R4,
        BHistOctaTupleNameCertCarrierAdmission_decode R5,
        BHistOctaTupleNameCertCarrierAdmission_decode R6,
        BHistOctaTupleNameCertCarrierAdmission_decode R7,
        BHistOctaTupleNameCertCarrierAdmission_decode H,
        BHistOctaTupleNameCertCarrierAdmission_decode C,
        BHistOctaTupleNameCertCarrierAdmission_decode P,
        BHistOctaTupleNameCertCarrierAdmission_decode L]

private theorem BHistOctaTupleNameCertCarrierAdmission_injective
    {x y : BHistOctaTupleNameCertUp} :
    bHistOctaTupleNameCertToEventFlow x = bHistOctaTupleNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistOctaTupleNameCertFromEventFlow (bHistOctaTupleNameCertToEventFlow x) =
        bHistOctaTupleNameCertFromEventFlow (bHistOctaTupleNameCertToEventFlow y) :=
    congrArg bHistOctaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistOctaTupleNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistOctaTupleNameCertCarrierAdmission_round_trip y)))

private theorem BHistOctaTupleNameCertCarrierAdmission_field_faithful :
    forall x y : BHistOctaTupleNameCertUp,
      bHistOctaTupleNameCertFields x = bHistOctaTupleNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 H1 C1 P1 L1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bHistOctaTupleNameCertBHistCarrier : BHistCarrier BHistOctaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistOctaTupleNameCertToEventFlow
  fromEventFlow := bHistOctaTupleNameCertFromEventFlow

instance bHistOctaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistOctaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistOctaTupleNameCertFromEventFlow (bHistOctaTupleNameCertToEventFlow x) = some x
    exact BHistOctaTupleNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistOctaTupleNameCertCarrierAdmission_injective heq)

instance bHistOctaTupleNameCertFieldFaithful : FieldFaithful BHistOctaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistOctaTupleNameCertFields
  field_faithful := BHistOctaTupleNameCertCarrierAdmission_field_faithful

theorem BHistOctaTupleNameCertCarrierAdmission
    {R0 R1 R2 R3 R4 R5 R6 R7 H C P L : BHist} :
    bHistOctaTupleNameCertFields
        (BHistOctaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 H C P L) =
      [R0, R1, R2, R3, R4, R5, R6, R7, H, C, P, L] ∧
        bHistOctaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.BHistOctaTupleNameCertUp
