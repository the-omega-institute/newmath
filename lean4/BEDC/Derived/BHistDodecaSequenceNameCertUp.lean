import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistDodecaSequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistDodecaSequenceNameCertUp : Type where
  | mk (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 H C P N : BHist) :
      BHistDodecaSequenceNameCertUp
  deriving DecidableEq

def bHistDodecaSequenceNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistDodecaSequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistDodecaSequenceNameCertEncodeBHist h

def bHistDodecaSequenceNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistDodecaSequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistDodecaSequenceNameCertDecodeBHist tail)

private theorem bHistDodecaSequenceNameCert_decode_encode :
    forall h : BHist,
      bHistDodecaSequenceNameCertDecodeBHist
        (bHistDodecaSequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistDodecaSequenceNameCertFields :
    BHistDodecaSequenceNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDodecaSequenceNameCertUp.mk S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 H C P N =>
      [S0, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, H, C, P, N]

def bHistDodecaSequenceNameCertToEventFlow :
    BHistDodecaSequenceNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistDodecaSequenceNameCertUp.mk S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 H C P N =>
      [[BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist S0,
        [BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist S1,
        [BMark.b0, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist S2,
        [BMark.b0, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist S3,
        [BMark.b1, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist S4,
        [BMark.b1, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist S5,
        [BMark.b0, BMark.b0, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist S6,
        [BMark.b0, BMark.b0, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist S7,
        [BMark.b0, BMark.b1, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist S8,
        [BMark.b0, BMark.b1, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist S9,
        [BMark.b1, BMark.b0, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist S10,
        [BMark.b1, BMark.b0, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist S11,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist C,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0],
        bHistDodecaSequenceNameCertEncodeBHist P,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b1],
        bHistDodecaSequenceNameCertEncodeBHist N]

private def bHistDodecaSequenceNameCertDecodePacket
    (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 H C P N : RawEvent) :
    BHistDodecaSequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistDodecaSequenceNameCertUp.mk
    (bHistDodecaSequenceNameCertDecodeBHist S0)
    (bHistDodecaSequenceNameCertDecodeBHist S1)
    (bHistDodecaSequenceNameCertDecodeBHist S2)
    (bHistDodecaSequenceNameCertDecodeBHist S3)
    (bHistDodecaSequenceNameCertDecodeBHist S4)
    (bHistDodecaSequenceNameCertDecodeBHist S5)
    (bHistDodecaSequenceNameCertDecodeBHist S6)
    (bHistDodecaSequenceNameCertDecodeBHist S7)
    (bHistDodecaSequenceNameCertDecodeBHist S8)
    (bHistDodecaSequenceNameCertDecodeBHist S9)
    (bHistDodecaSequenceNameCertDecodeBHist S10)
    (bHistDodecaSequenceNameCertDecodeBHist S11)
    (bHistDodecaSequenceNameCertDecodeBHist H)
    (bHistDodecaSequenceNameCertDecodeBHist C)
    (bHistDodecaSequenceNameCertDecodeBHist P)
    (bHistDodecaSequenceNameCertDecodeBHist N)

private def bHistDodecaSequenceNameCertRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => bHistDodecaSequenceNameCertRawAt n rest

private def bHistDodecaSequenceNameCertLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => bHistDodecaSequenceNameCertLengthEq n rest

def bHistDodecaSequenceNameCertFromEventFlow :
    EventFlow -> Option BHistDodecaSequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match bHistDodecaSequenceNameCertLengthEq 32 flow with
      | true =>
          some
            (bHistDodecaSequenceNameCertDecodePacket
              (bHistDodecaSequenceNameCertRawAt 1 flow)
              (bHistDodecaSequenceNameCertRawAt 3 flow)
              (bHistDodecaSequenceNameCertRawAt 5 flow)
              (bHistDodecaSequenceNameCertRawAt 7 flow)
              (bHistDodecaSequenceNameCertRawAt 9 flow)
              (bHistDodecaSequenceNameCertRawAt 11 flow)
              (bHistDodecaSequenceNameCertRawAt 13 flow)
              (bHistDodecaSequenceNameCertRawAt 15 flow)
              (bHistDodecaSequenceNameCertRawAt 17 flow)
              (bHistDodecaSequenceNameCertRawAt 19 flow)
              (bHistDodecaSequenceNameCertRawAt 21 flow)
              (bHistDodecaSequenceNameCertRawAt 23 flow)
              (bHistDodecaSequenceNameCertRawAt 25 flow)
              (bHistDodecaSequenceNameCertRawAt 27 flow)
              (bHistDodecaSequenceNameCertRawAt 29 flow)
              (bHistDodecaSequenceNameCertRawAt 31 flow))
      | false => none

private theorem bHistDodecaSequenceNameCert_round_trip :
    forall x : BHistDodecaSequenceNameCertUp,
      bHistDodecaSequenceNameCertFromEventFlow
        (bHistDodecaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 H C P N =>
      change
        some
          (bHistDodecaSequenceNameCertDecodePacket
            (bHistDodecaSequenceNameCertEncodeBHist S0)
            (bHistDodecaSequenceNameCertEncodeBHist S1)
            (bHistDodecaSequenceNameCertEncodeBHist S2)
            (bHistDodecaSequenceNameCertEncodeBHist S3)
            (bHistDodecaSequenceNameCertEncodeBHist S4)
            (bHistDodecaSequenceNameCertEncodeBHist S5)
            (bHistDodecaSequenceNameCertEncodeBHist S6)
            (bHistDodecaSequenceNameCertEncodeBHist S7)
            (bHistDodecaSequenceNameCertEncodeBHist S8)
            (bHistDodecaSequenceNameCertEncodeBHist S9)
            (bHistDodecaSequenceNameCertEncodeBHist S10)
            (bHistDodecaSequenceNameCertEncodeBHist S11)
            (bHistDodecaSequenceNameCertEncodeBHist H)
            (bHistDodecaSequenceNameCertEncodeBHist C)
            (bHistDodecaSequenceNameCertEncodeBHist P)
            (bHistDodecaSequenceNameCertEncodeBHist N)) =
          some
            (BHistDodecaSequenceNameCertUp.mk S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 H C P N)
      unfold bHistDodecaSequenceNameCertDecodePacket
      rw [bHistDodecaSequenceNameCert_decode_encode S0,
        bHistDodecaSequenceNameCert_decode_encode S1,
        bHistDodecaSequenceNameCert_decode_encode S2,
        bHistDodecaSequenceNameCert_decode_encode S3,
        bHistDodecaSequenceNameCert_decode_encode S4,
        bHistDodecaSequenceNameCert_decode_encode S5,
        bHistDodecaSequenceNameCert_decode_encode S6,
        bHistDodecaSequenceNameCert_decode_encode S7,
        bHistDodecaSequenceNameCert_decode_encode S8,
        bHistDodecaSequenceNameCert_decode_encode S9,
        bHistDodecaSequenceNameCert_decode_encode S10,
        bHistDodecaSequenceNameCert_decode_encode S11,
        bHistDodecaSequenceNameCert_decode_encode H,
        bHistDodecaSequenceNameCert_decode_encode C,
        bHistDodecaSequenceNameCert_decode_encode P,
        bHistDodecaSequenceNameCert_decode_encode N]

private theorem bHistDodecaSequenceNameCertToEventFlow_injective
    {x y : BHistDodecaSequenceNameCertUp} :
    bHistDodecaSequenceNameCertToEventFlow x =
        bHistDodecaSequenceNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistDodecaSequenceNameCertFromEventFlow
          (bHistDodecaSequenceNameCertToEventFlow x) =
        bHistDodecaSequenceNameCertFromEventFlow
          (bHistDodecaSequenceNameCertToEventFlow y) :=
    congrArg bHistDodecaSequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistDodecaSequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistDodecaSequenceNameCert_round_trip y)))

private theorem bHistDodecaSequenceNameCert_field_faithful :
    forall x y : BHistDodecaSequenceNameCertUp,
      bHistDodecaSequenceNameCertFields x =
        bHistDodecaSequenceNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S01 S11 S21 S31 S41 S51 S61 S71 S81 S91 S101 S111 H1 C1 P1 N1 =>
      cases y with
      | mk S02 S12 S22 S32 S42 S52 S62 S72 S82 S92 S102 S112 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bHistDodecaSequenceNameCertBHistCarrier :
    BHistCarrier BHistDodecaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistDodecaSequenceNameCertToEventFlow
  fromEventFlow := bHistDodecaSequenceNameCertFromEventFlow

instance bHistDodecaSequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistDodecaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistDodecaSequenceNameCertFromEventFlow
          (bHistDodecaSequenceNameCertToEventFlow x) = some x
    exact bHistDodecaSequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistDodecaSequenceNameCertToEventFlow_injective heq)

instance bHistDodecaSequenceNameCertFieldFaithful :
    FieldFaithful BHistDodecaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistDodecaSequenceNameCertFields
  field_faithful := bHistDodecaSequenceNameCert_field_faithful

def taste_gate : ChapterTasteGate BHistDodecaSequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistDodecaSequenceNameCertChapterTasteGate

theorem BHistDodecaSequenceNameCertTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bHistDodecaSequenceNameCertDecodeBHist (bHistDodecaSequenceNameCertEncodeBHist h) = h) ∧
      (forall x : BHistDodecaSequenceNameCertUp,
        bHistDodecaSequenceNameCertFromEventFlow
          (bHistDodecaSequenceNameCertToEventFlow x) = some x) ∧
        (forall x y : BHistDodecaSequenceNameCertUp,
          bHistDodecaSequenceNameCertToEventFlow x =
            bHistDodecaSequenceNameCertToEventFlow y -> x = y) ∧
          bHistDodecaSequenceNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨bHistDodecaSequenceNameCert_decode_encode,
      bHistDodecaSequenceNameCert_round_trip,
      (fun _ _ heq => bHistDodecaSequenceNameCertToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BHistDodecaSequenceNameCertUp
