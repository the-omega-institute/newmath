import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistDodecaCarrierNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistDodecaCarrierNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P N : BHist) :
      BHistDodecaCarrierNameCertUp
  deriving DecidableEq

def bHistDodecaCarrierNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistDodecaCarrierNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistDodecaCarrierNameCertEncodeBHist h

def bHistDodecaCarrierNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistDodecaCarrierNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistDodecaCarrierNameCertDecodeBHist tail)

private theorem bHistDodecaCarrierNameCert_decode_encode :
    forall h : BHist,
      bHistDodecaCarrierNameCertDecodeBHist
        (bHistDodecaCarrierNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistDodecaCarrierNameCertFields : BHistDodecaCarrierNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDodecaCarrierNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P N =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, H, C, P, N]

def bHistDodecaCarrierNameCertToEventFlow : BHistDodecaCarrierNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDodecaCarrierNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P N =>
      [[BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist R0,
        [BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist R1,
        [BMark.b0, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist R2,
        [BMark.b0, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist R3,
        [BMark.b1, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist R5,
        [BMark.b0, BMark.b0, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist R6,
        [BMark.b0, BMark.b0, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist R7,
        [BMark.b0, BMark.b1, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist R8,
        [BMark.b0, BMark.b1, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist R9,
        [BMark.b1, BMark.b0, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist R10,
        [BMark.b1, BMark.b0, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist R11,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist C,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0],
        bHistDodecaCarrierNameCertEncodeBHist P,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b1],
        bHistDodecaCarrierNameCertEncodeBHist N]

private def bHistDodecaCarrierNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P N : RawEvent) :
    BHistDodecaCarrierNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistDodecaCarrierNameCertUp.mk
    (bHistDodecaCarrierNameCertDecodeBHist R0)
    (bHistDodecaCarrierNameCertDecodeBHist R1)
    (bHistDodecaCarrierNameCertDecodeBHist R2)
    (bHistDodecaCarrierNameCertDecodeBHist R3)
    (bHistDodecaCarrierNameCertDecodeBHist R4)
    (bHistDodecaCarrierNameCertDecodeBHist R5)
    (bHistDodecaCarrierNameCertDecodeBHist R6)
    (bHistDodecaCarrierNameCertDecodeBHist R7)
    (bHistDodecaCarrierNameCertDecodeBHist R8)
    (bHistDodecaCarrierNameCertDecodeBHist R9)
    (bHistDodecaCarrierNameCertDecodeBHist R10)
    (bHistDodecaCarrierNameCertDecodeBHist R11)
    (bHistDodecaCarrierNameCertDecodeBHist H)
    (bHistDodecaCarrierNameCertDecodeBHist C)
    (bHistDodecaCarrierNameCertDecodeBHist P)
    (bHistDodecaCarrierNameCertDecodeBHist N)

private def bHistDodecaCarrierNameCertRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => bHistDodecaCarrierNameCertRawAt n rest

private def bHistDodecaCarrierNameCertLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => bHistDodecaCarrierNameCertLengthEq n rest

def bHistDodecaCarrierNameCertFromEventFlow :
    EventFlow -> Option BHistDodecaCarrierNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match bHistDodecaCarrierNameCertLengthEq 32 flow with
      | true =>
          some
            (bHistDodecaCarrierNameCertDecodePacket
              (bHistDodecaCarrierNameCertRawAt 1 flow)
              (bHistDodecaCarrierNameCertRawAt 3 flow)
              (bHistDodecaCarrierNameCertRawAt 5 flow)
              (bHistDodecaCarrierNameCertRawAt 7 flow)
              (bHistDodecaCarrierNameCertRawAt 9 flow)
              (bHistDodecaCarrierNameCertRawAt 11 flow)
              (bHistDodecaCarrierNameCertRawAt 13 flow)
              (bHistDodecaCarrierNameCertRawAt 15 flow)
              (bHistDodecaCarrierNameCertRawAt 17 flow)
              (bHistDodecaCarrierNameCertRawAt 19 flow)
              (bHistDodecaCarrierNameCertRawAt 21 flow)
              (bHistDodecaCarrierNameCertRawAt 23 flow)
              (bHistDodecaCarrierNameCertRawAt 25 flow)
              (bHistDodecaCarrierNameCertRawAt 27 flow)
              (bHistDodecaCarrierNameCertRawAt 29 flow)
              (bHistDodecaCarrierNameCertRawAt 31 flow))
      | false => none

private theorem bHistDodecaCarrierNameCert_round_trip :
    forall x : BHistDodecaCarrierNameCertUp,
      bHistDodecaCarrierNameCertFromEventFlow
        (bHistDodecaCarrierNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H C P N =>
      change
        some
          (bHistDodecaCarrierNameCertDecodePacket
            (bHistDodecaCarrierNameCertEncodeBHist R0)
            (bHistDodecaCarrierNameCertEncodeBHist R1)
            (bHistDodecaCarrierNameCertEncodeBHist R2)
            (bHistDodecaCarrierNameCertEncodeBHist R3)
            (bHistDodecaCarrierNameCertEncodeBHist R4)
            (bHistDodecaCarrierNameCertEncodeBHist R5)
            (bHistDodecaCarrierNameCertEncodeBHist R6)
            (bHistDodecaCarrierNameCertEncodeBHist R7)
            (bHistDodecaCarrierNameCertEncodeBHist R8)
            (bHistDodecaCarrierNameCertEncodeBHist R9)
            (bHistDodecaCarrierNameCertEncodeBHist R10)
            (bHistDodecaCarrierNameCertEncodeBHist R11)
            (bHistDodecaCarrierNameCertEncodeBHist H)
            (bHistDodecaCarrierNameCertEncodeBHist C)
            (bHistDodecaCarrierNameCertEncodeBHist P)
            (bHistDodecaCarrierNameCertEncodeBHist N)) =
          some
            (BHistDodecaCarrierNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11
              H C P N)
      unfold bHistDodecaCarrierNameCertDecodePacket
      rw [bHistDodecaCarrierNameCert_decode_encode R0,
        bHistDodecaCarrierNameCert_decode_encode R1,
        bHistDodecaCarrierNameCert_decode_encode R2,
        bHistDodecaCarrierNameCert_decode_encode R3,
        bHistDodecaCarrierNameCert_decode_encode R4,
        bHistDodecaCarrierNameCert_decode_encode R5,
        bHistDodecaCarrierNameCert_decode_encode R6,
        bHistDodecaCarrierNameCert_decode_encode R7,
        bHistDodecaCarrierNameCert_decode_encode R8,
        bHistDodecaCarrierNameCert_decode_encode R9,
        bHistDodecaCarrierNameCert_decode_encode R10,
        bHistDodecaCarrierNameCert_decode_encode R11,
        bHistDodecaCarrierNameCert_decode_encode H,
        bHistDodecaCarrierNameCert_decode_encode C,
        bHistDodecaCarrierNameCert_decode_encode P,
        bHistDodecaCarrierNameCert_decode_encode N]

private theorem bHistDodecaCarrierNameCertToEventFlow_injective
    {x y : BHistDodecaCarrierNameCertUp} :
    bHistDodecaCarrierNameCertToEventFlow x =
        bHistDodecaCarrierNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistDodecaCarrierNameCertFromEventFlow
          (bHistDodecaCarrierNameCertToEventFlow x) =
        bHistDodecaCarrierNameCertFromEventFlow
          (bHistDodecaCarrierNameCertToEventFlow y) :=
    congrArg bHistDodecaCarrierNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistDodecaCarrierNameCert_round_trip x).symm
      (Eq.trans hread (bHistDodecaCarrierNameCert_round_trip y)))

private theorem bHistDodecaCarrierNameCert_field_faithful :
    forall x y : BHistDodecaCarrierNameCertUp,
      bHistDodecaCarrierNameCertFields x = bHistDodecaCarrierNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 R111 H1 C1 P1 N1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 R112 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bHistDodecaCarrierNameCertBHistCarrier :
    BHistCarrier BHistDodecaCarrierNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistDodecaCarrierNameCertToEventFlow
  fromEventFlow := bHistDodecaCarrierNameCertFromEventFlow

instance taste_gate : ChapterTasteGate BHistDodecaCarrierNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistDodecaCarrierNameCertFromEventFlow
          (bHistDodecaCarrierNameCertToEventFlow x) = some x
    exact bHistDodecaCarrierNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistDodecaCarrierNameCertToEventFlow_injective heq)

instance bHistDodecaCarrierNameCertFieldFaithful :
    FieldFaithful BHistDodecaCarrierNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistDodecaCarrierNameCertFields
  field_faithful := bHistDodecaCarrierNameCert_field_faithful

theorem BHistDodecaCarrierNameCertUp_single_carrier_alignment :
    (forall x : BHistDodecaCarrierNameCertUp,
      bHistDodecaCarrierNameCertFromEventFlow
        (bHistDodecaCarrierNameCertToEventFlow x) = some x) ∧
      (forall x y : BHistDodecaCarrierNameCertUp,
        bHistDodecaCarrierNameCertToEventFlow x =
          bHistDodecaCarrierNameCertToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bHistDodecaCarrierNameCert_round_trip,
      fun _ _ heq => bHistDodecaCarrierNameCertToEventFlow_injective heq⟩

end BEDC.Derived.BHistDodecaCarrierNameCertUp
