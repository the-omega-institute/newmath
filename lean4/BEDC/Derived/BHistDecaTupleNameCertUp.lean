import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistDecaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistDecaTupleNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L : BHist) :
      BHistDecaTupleNameCertUp
  deriving DecidableEq

def bHistDecaTupleNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistDecaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistDecaTupleNameCertEncodeBHist h

def bHistDecaTupleNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistDecaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistDecaTupleNameCertDecodeBHist tail)

private theorem BHistDecaTupleNameCertCarrierAdmission_decode :
    forall h : BHist, bHistDecaTupleNameCertDecodeBHist
      (bHistDecaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistDecaTupleNameCertFields : BHistDecaTupleNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, H, C, P, L]

def bHistDecaTupleNameCertToEventFlow : BHistDecaTupleNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L =>
      [[BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R0,
        [BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R7,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R8,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist R9,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistDecaTupleNameCertEncodeBHist L]

private def bHistDecaTupleNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L : RawEvent) :
    BHistDecaTupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistDecaTupleNameCertUp.mk
    (bHistDecaTupleNameCertDecodeBHist R0)
    (bHistDecaTupleNameCertDecodeBHist R1)
    (bHistDecaTupleNameCertDecodeBHist R2)
    (bHistDecaTupleNameCertDecodeBHist R3)
    (bHistDecaTupleNameCertDecodeBHist R4)
    (bHistDecaTupleNameCertDecodeBHist R5)
    (bHistDecaTupleNameCertDecodeBHist R6)
    (bHistDecaTupleNameCertDecodeBHist R7)
    (bHistDecaTupleNameCertDecodeBHist R8)
    (bHistDecaTupleNameCertDecodeBHist R9)
    (bHistDecaTupleNameCertDecodeBHist H)
    (bHistDecaTupleNameCertDecodeBHist C)
    (bHistDecaTupleNameCertDecodeBHist P)
    (bHistDecaTupleNameCertDecodeBHist L)

def bHistDecaTupleNameCertFromEventFlow : EventFlow -> Option BHistDecaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, R0, _tag1, R1, _tag2, R2, _tag3, R3, _tag4, R4, _tag5, R5, _tag6, R6,
      _tag7, R7, _tag8, R8, _tag9, R9, _tag10, H, _tag11, C, _tag12, P, _tag13, L] =>
      some (bHistDecaTupleNameCertDecodePacket R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L)
  | _ => none

private theorem BHistDecaTupleNameCertCarrierAdmission_round_trip :
    forall x : BHistDecaTupleNameCertUp,
      bHistDecaTupleNameCertFromEventFlow (bHistDecaTupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L =>
      change
        some
          (bHistDecaTupleNameCertDecodePacket
            (bHistDecaTupleNameCertEncodeBHist R0)
            (bHistDecaTupleNameCertEncodeBHist R1)
            (bHistDecaTupleNameCertEncodeBHist R2)
            (bHistDecaTupleNameCertEncodeBHist R3)
            (bHistDecaTupleNameCertEncodeBHist R4)
            (bHistDecaTupleNameCertEncodeBHist R5)
            (bHistDecaTupleNameCertEncodeBHist R6)
            (bHistDecaTupleNameCertEncodeBHist R7)
            (bHistDecaTupleNameCertEncodeBHist R8)
            (bHistDecaTupleNameCertEncodeBHist R9)
            (bHistDecaTupleNameCertEncodeBHist H)
            (bHistDecaTupleNameCertEncodeBHist C)
            (bHistDecaTupleNameCertEncodeBHist P)
            (bHistDecaTupleNameCertEncodeBHist L)) =
          some (BHistDecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L)
      unfold bHistDecaTupleNameCertDecodePacket
      rw [BHistDecaTupleNameCertCarrierAdmission_decode R0,
        BHistDecaTupleNameCertCarrierAdmission_decode R1,
        BHistDecaTupleNameCertCarrierAdmission_decode R2,
        BHistDecaTupleNameCertCarrierAdmission_decode R3,
        BHistDecaTupleNameCertCarrierAdmission_decode R4,
        BHistDecaTupleNameCertCarrierAdmission_decode R5,
        BHistDecaTupleNameCertCarrierAdmission_decode R6,
        BHistDecaTupleNameCertCarrierAdmission_decode R7,
        BHistDecaTupleNameCertCarrierAdmission_decode R8,
        BHistDecaTupleNameCertCarrierAdmission_decode R9,
        BHistDecaTupleNameCertCarrierAdmission_decode H,
        BHistDecaTupleNameCertCarrierAdmission_decode C,
        BHistDecaTupleNameCertCarrierAdmission_decode P,
        BHistDecaTupleNameCertCarrierAdmission_decode L]

private theorem BHistDecaTupleNameCertCarrierAdmission_injective
    {x y : BHistDecaTupleNameCertUp} :
    bHistDecaTupleNameCertToEventFlow x = bHistDecaTupleNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistDecaTupleNameCertFromEventFlow (bHistDecaTupleNameCertToEventFlow x) =
        bHistDecaTupleNameCertFromEventFlow (bHistDecaTupleNameCertToEventFlow y) :=
    congrArg bHistDecaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistDecaTupleNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistDecaTupleNameCertCarrierAdmission_round_trip y)))

private theorem BHistDecaTupleNameCertCarrierAdmission_field_faithful :
    forall x y : BHistDecaTupleNameCertUp,
      bHistDecaTupleNameCertFields x = bHistDecaTupleNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 H1 C1 P1 L1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bHistDecaTupleNameCertBHistCarrier : BHistCarrier BHistDecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistDecaTupleNameCertToEventFlow
  fromEventFlow := bHistDecaTupleNameCertFromEventFlow

instance bHistDecaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistDecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistDecaTupleNameCertFromEventFlow (bHistDecaTupleNameCertToEventFlow x) = some x
    exact BHistDecaTupleNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistDecaTupleNameCertCarrierAdmission_injective heq)

instance bHistDecaTupleNameCertFieldFaithful : FieldFaithful BHistDecaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistDecaTupleNameCertFields
  field_faithful := BHistDecaTupleNameCertCarrierAdmission_field_faithful

theorem BHistDecaTupleNameCertCarrierAdmission
    {R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L : BHist} :
    bHistDecaTupleNameCertFields
        (BHistDecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H C P L) =
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, H, C, P, L] ∧
        bHistDecaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.BHistDecaTupleNameCertUp
