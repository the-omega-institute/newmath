import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuotientStreamRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuotientStreamRefusalUp : Type where
  | mk :
      (stream sealRow refusal route ledger witness nameCert : BHist) →
        QuotientStreamRefusalUp
  deriving DecidableEq

def quotientStreamRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quotientStreamRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quotientStreamRefusalEncodeBHist h

def quotientStreamRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quotientStreamRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quotientStreamRefusalDecodeBHist tail)

private theorem quotientStreamRefusal_decode_encode_bhist :
    ∀ h : BHist,
      quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def quotientStreamRefusalToEventFlow : QuotientStreamRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | QuotientStreamRefusalUp.mk stream sealRow refusal route ledger witness nameCert =>
      [[BMark.b0],
        quotientStreamRefusalEncodeBHist stream,
        [BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist nameCert]

private def quotientStreamRefusalRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => quotientStreamRefusalRawAt n rest

private def quotientStreamRefusalLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => quotientStreamRefusalLengthEq n rest

def quotientStreamRefusalFromEventFlow : EventFlow → Option QuotientStreamRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match quotientStreamRefusalLengthEq 14 flow with
      | true =>
          some
            (QuotientStreamRefusalUp.mk
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 1 flow))
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 3 flow))
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 5 flow))
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 7 flow))
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 9 flow))
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 11 flow))
              (quotientStreamRefusalDecodeBHist (quotientStreamRefusalRawAt 13 flow)))
      | false => none

private theorem quotientStreamRefusal_round_trip :
    ∀ x : QuotientStreamRefusalUp,
      quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream sealRow refusal route ledger witness nameCert =>
      change
        some
          (QuotientStreamRefusalUp.mk
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist stream))
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist sealRow))
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist refusal))
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist route))
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist ledger))
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist witness))
            (quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist nameCert))) =
          some
            (QuotientStreamRefusalUp.mk stream sealRow refusal route ledger witness nameCert)
      rw [quotientStreamRefusal_decode_encode_bhist stream,
        quotientStreamRefusal_decode_encode_bhist sealRow,
        quotientStreamRefusal_decode_encode_bhist refusal,
        quotientStreamRefusal_decode_encode_bhist route,
        quotientStreamRefusal_decode_encode_bhist ledger,
        quotientStreamRefusal_decode_encode_bhist witness,
        quotientStreamRefusal_decode_encode_bhist nameCert]

private theorem quotientStreamRefusalToEventFlow_injective {x y : QuotientStreamRefusalUp} :
    quotientStreamRefusalToEventFlow x = quotientStreamRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) =
        quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow y) :=
    congrArg quotientStreamRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (quotientStreamRefusal_round_trip x).symm
      (Eq.trans hread (quotientStreamRefusal_round_trip y)))

instance quotientStreamRefusalBHistCarrier : BHistCarrier QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quotientStreamRefusalToEventFlow
  fromEventFlow := quotientStreamRefusalFromEventFlow

instance quotientStreamRefusalChapterTasteGate :
    ChapterTasteGate QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) = some x
    exact quotientStreamRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (quotientStreamRefusalToEventFlow_injective heq)

instance quotientStreamRefusalFieldFaithful : FieldFaithful QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | QuotientStreamRefusalUp.mk stream sealRow refusal route ledger witness nameCert =>
        [stream, sealRow, refusal, route, ledger, witness, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk stream1 sealRow1 refusal1 route1 ledger1 witness1 nameCert1 =>
        cases y with
        | mk stream2 sealRow2 refusal2 route2 ledger2 witness2 nameCert2 =>
            cases h
            rfl

instance quotientStreamRefusalNontrivial : Nontrivial QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuotientStreamRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      QuotientStreamRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate QuotientStreamRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quotientStreamRefusalChapterTasteGate

theorem QuotientStreamRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist h) = h) ∧
      (∀ x : QuotientStreamRefusalUp,
        quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) = some x) ∧
        (∀ x y : QuotientStreamRefusalUp,
          quotientStreamRefusalToEventFlow x = quotientStreamRefusalToEventFlow y → x = y) ∧
          quotientStreamRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨quotientStreamRefusal_decode_encode_bhist,
      quotientStreamRefusal_round_trip,
      by
        intro x y heq
        exact quotientStreamRefusalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.QuotientStreamRefusalUp
