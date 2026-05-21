import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistHexaSequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistHexaSequenceNameCertUp : Type where
  | mk (a b c d e f : BHist) : BHistHexaSequenceNameCertUp
  deriving DecidableEq

def bHistHexaSequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistHexaSequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistHexaSequenceNameCertEncodeBHist h

def bHistHexaSequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistHexaSequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistHexaSequenceNameCertDecodeBHist tail)

private theorem bHistHexaSequenceNameCert_decode_encode :
    ∀ h : BHist,
      bHistHexaSequenceNameCertDecodeBHist
        (bHistHexaSequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistHexaSequenceNameCertFields :
    BHistHexaSequenceNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHexaSequenceNameCertUp.mk a b c d e f => [a, b, c, d, e, f]

def bHistHexaSequenceNameCertToEventFlow :
    BHistHexaSequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHexaSequenceNameCertUp.mk a b c d e f =>
      [[BMark.b0],
        bHistHexaSequenceNameCertEncodeBHist a,
        [BMark.b1, BMark.b0],
        bHistHexaSequenceNameCertEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistHexaSequenceNameCertEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHexaSequenceNameCertEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHexaSequenceNameCertEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHexaSequenceNameCertEncodeBHist f]

private def bHistHexaSequenceNameCertDecodePacket
    (a b c d e f : RawEvent) : BHistHexaSequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistHexaSequenceNameCertUp.mk
    (bHistHexaSequenceNameCertDecodeBHist a)
    (bHistHexaSequenceNameCertDecodeBHist b)
    (bHistHexaSequenceNameCertDecodeBHist c)
    (bHistHexaSequenceNameCertDecodeBHist d)
    (bHistHexaSequenceNameCertDecodeBHist e)
    (bHistHexaSequenceNameCertDecodeBHist f)

private def bHistHexaSequenceNameCertRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => bHistHexaSequenceNameCertRawAt n rest

private def bHistHexaSequenceNameCertLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => bHistHexaSequenceNameCertLengthEq n rest

def bHistHexaSequenceNameCertFromEventFlow :
    EventFlow → Option BHistHexaSequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match bHistHexaSequenceNameCertLengthEq 12 flow with
      | true =>
          some
            (bHistHexaSequenceNameCertDecodePacket
              (bHistHexaSequenceNameCertRawAt 1 flow)
              (bHistHexaSequenceNameCertRawAt 3 flow)
              (bHistHexaSequenceNameCertRawAt 5 flow)
              (bHistHexaSequenceNameCertRawAt 7 flow)
              (bHistHexaSequenceNameCertRawAt 9 flow)
              (bHistHexaSequenceNameCertRawAt 11 flow))
      | false => none

private theorem bHistHexaSequenceNameCert_round_trip :
    ∀ x : BHistHexaSequenceNameCertUp,
      bHistHexaSequenceNameCertFromEventFlow
        (bHistHexaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a b c d e f =>
      change
        some
          (bHistHexaSequenceNameCertDecodePacket
            (bHistHexaSequenceNameCertEncodeBHist a)
            (bHistHexaSequenceNameCertEncodeBHist b)
            (bHistHexaSequenceNameCertEncodeBHist c)
            (bHistHexaSequenceNameCertEncodeBHist d)
            (bHistHexaSequenceNameCertEncodeBHist e)
            (bHistHexaSequenceNameCertEncodeBHist f)) =
          some (BHistHexaSequenceNameCertUp.mk a b c d e f)
      unfold bHistHexaSequenceNameCertDecodePacket
      rw [bHistHexaSequenceNameCert_decode_encode a,
        bHistHexaSequenceNameCert_decode_encode b,
        bHistHexaSequenceNameCert_decode_encode c,
        bHistHexaSequenceNameCert_decode_encode d,
        bHistHexaSequenceNameCert_decode_encode e,
        bHistHexaSequenceNameCert_decode_encode f]

private theorem bHistHexaSequenceNameCertToEventFlow_injective
    {x y : BHistHexaSequenceNameCertUp} :
    bHistHexaSequenceNameCertToEventFlow x =
        bHistHexaSequenceNameCertToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistHexaSequenceNameCertFromEventFlow
          (bHistHexaSequenceNameCertToEventFlow x) =
        bHistHexaSequenceNameCertFromEventFlow
          (bHistHexaSequenceNameCertToEventFlow y) :=
    congrArg bHistHexaSequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (bHistHexaSequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistHexaSequenceNameCert_round_trip y)))

private theorem bHistHexaSequenceNameCert_field_faithful :
    ∀ x y : BHistHexaSequenceNameCertUp,
      bHistHexaSequenceNameCertFields x =
          bHistHexaSequenceNameCertFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk a1 b1 c1 d1 e1 f1 =>
      cases y with
      | mk a2 b2 c2 d2 e2 f2 =>
          cases hfields
          rfl

instance bHistHexaSequenceNameCertBHistCarrier :
    BHistCarrier BHistHexaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistHexaSequenceNameCertToEventFlow
  fromEventFlow := bHistHexaSequenceNameCertFromEventFlow

instance bHistHexaSequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistHexaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistHexaSequenceNameCertFromEventFlow
          (bHistHexaSequenceNameCertToEventFlow x) = some x
    exact bHistHexaSequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistHexaSequenceNameCertToEventFlow_injective heq)

instance bHistHexaSequenceNameCertFieldFaithful :
    FieldFaithful BHistHexaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistHexaSequenceNameCertFields
  field_faithful := bHistHexaSequenceNameCert_field_faithful

instance bHistHexaSequenceNameCertNontrivial :
    Nontrivial BHistHexaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistHexaSequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BHistHexaSequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BHistHexaSequenceNameCertUp_single_carrier_alignment :
    (forall x : BHistHexaSequenceNameCertUp,
      bHistHexaSequenceNameCertFromEventFlow
          (bHistHexaSequenceNameCertToEventFlow x) = some x) ∧
      (forall x y : BHistHexaSequenceNameCertUp,
        bHistHexaSequenceNameCertToEventFlow x =
            bHistHexaSequenceNameCertToEventFlow y ->
          x = y) ∧
        (forall x y : BHistHexaSequenceNameCertUp,
          bHistHexaSequenceNameCertFields x =
              bHistHexaSequenceNameCertFields y ->
            x = y) ∧
          bHistHexaSequenceNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk a b c d e f =>
        change
          some
            (bHistHexaSequenceNameCertDecodePacket
              (bHistHexaSequenceNameCertEncodeBHist a)
              (bHistHexaSequenceNameCertEncodeBHist b)
              (bHistHexaSequenceNameCertEncodeBHist c)
              (bHistHexaSequenceNameCertEncodeBHist d)
              (bHistHexaSequenceNameCertEncodeBHist e)
              (bHistHexaSequenceNameCertEncodeBHist f)) =
            some (BHistHexaSequenceNameCertUp.mk a b c d e f)
        unfold bHistHexaSequenceNameCertDecodePacket
        rw [bHistHexaSequenceNameCert_decode_encode a,
          bHistHexaSequenceNameCert_decode_encode b,
          bHistHexaSequenceNameCert_decode_encode c,
          bHistHexaSequenceNameCert_decode_encode d,
          bHistHexaSequenceNameCert_decode_encode e,
          bHistHexaSequenceNameCert_decode_encode f]
  · constructor
    · intro _ _ heq
      exact bHistHexaSequenceNameCertToEventFlow_injective heq
    · constructor
      · intro x y hfields
        cases x with
        | mk a1 b1 c1 d1 e1 f1 =>
            cases y with
            | mk a2 b2 c2 d2 e2 f2 =>
                cases hfields
                rfl
      · rfl

end BEDC.Derived.BHistHexaSequenceNameCertUp
