import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RatClassifierTransportSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RatClassifierTransportSealUp : Type where
  | mk :
      (rat classifier transport sealRow window stability ledger nameCert : BHist) →
        RatClassifierTransportSealUp
  deriving DecidableEq

def ratClassifierTransportSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ratClassifierTransportSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ratClassifierTransportSealEncodeBHist h

def ratClassifierTransportSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ratClassifierTransportSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ratClassifierTransportSealDecodeBHist tail)

private theorem ratClassifierTransportSeal_decode_encode_bhist :
    ∀ h : BHist,
      ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ratClassifierTransportSealToEventFlow : RatClassifierTransportSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RatClassifierTransportSealUp.mk rat classifier transport sealRow window stability ledger
      nameCert =>
      [[BMark.b0],
        ratClassifierTransportSealEncodeBHist rat,
        [BMark.b1, BMark.b0],
        ratClassifierTransportSealEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        ratClassifierTransportSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ratClassifierTransportSealEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ratClassifierTransportSealEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ratClassifierTransportSealEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ratClassifierTransportSealEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        ratClassifierTransportSealEncodeBHist nameCert]

private def ratClassifierTransportSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => ratClassifierTransportSealRawAt n rest

private def ratClassifierTransportSealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => ratClassifierTransportSealLengthEq n rest

def ratClassifierTransportSealFromEventFlow :
    EventFlow → Option RatClassifierTransportSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match ratClassifierTransportSealLengthEq 16 flow with
      | true =>
          some
            (RatClassifierTransportSealUp.mk
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 1 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 3 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 5 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 7 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 9 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 11 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 13 flow))
              (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealRawAt 15 flow)))
      | false => none

private theorem ratClassifierTransportSeal_round_trip :
    ∀ x : RatClassifierTransportSealUp,
      ratClassifierTransportSealFromEventFlow
        (ratClassifierTransportSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rat classifier transport sealRow window stability ledger nameCert =>
      change
        some
          (RatClassifierTransportSealUp.mk
            (ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealEncodeBHist rat))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist classifier))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist transport))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist sealRow))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist window))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist stability))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist ledger))
            (ratClassifierTransportSealDecodeBHist
              (ratClassifierTransportSealEncodeBHist nameCert))) =
          some
            (RatClassifierTransportSealUp.mk rat classifier transport sealRow window stability
              ledger nameCert)
      rw [ratClassifierTransportSeal_decode_encode_bhist rat,
        ratClassifierTransportSeal_decode_encode_bhist classifier,
        ratClassifierTransportSeal_decode_encode_bhist transport,
        ratClassifierTransportSeal_decode_encode_bhist sealRow,
        ratClassifierTransportSeal_decode_encode_bhist window,
        ratClassifierTransportSeal_decode_encode_bhist stability,
        ratClassifierTransportSeal_decode_encode_bhist ledger,
        ratClassifierTransportSeal_decode_encode_bhist nameCert]

private theorem ratClassifierTransportSealToEventFlow_injective
    {x y : RatClassifierTransportSealUp} :
    ratClassifierTransportSealToEventFlow x =
      ratClassifierTransportSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ratClassifierTransportSealFromEventFlow (ratClassifierTransportSealToEventFlow x) =
        ratClassifierTransportSealFromEventFlow (ratClassifierTransportSealToEventFlow y) :=
    congrArg ratClassifierTransportSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ratClassifierTransportSeal_round_trip x).symm
      (Eq.trans hread (ratClassifierTransportSeal_round_trip y)))

instance ratClassifierTransportSealBHistCarrier :
    BHistCarrier RatClassifierTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ratClassifierTransportSealToEventFlow
  fromEventFlow := ratClassifierTransportSealFromEventFlow

instance ratClassifierTransportSealChapterTasteGate :
    ChapterTasteGate RatClassifierTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ratClassifierTransportSealFromEventFlow
        (ratClassifierTransportSealToEventFlow x) = some x
    exact ratClassifierTransportSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ratClassifierTransportSealToEventFlow_injective heq)

instance ratClassifierTransportSealFieldFaithful :
    FieldFaithful RatClassifierTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RatClassifierTransportSealUp.mk rat classifier transport sealRow window stability ledger
        nameCert =>
        [rat, classifier, transport, sealRow, window, stability, ledger, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk rat1 classifier1 transport1 sealRow1 window1 stability1 ledger1 nameCert1 =>
        cases y with
        | mk rat2 classifier2 transport2 sealRow2 window2 stability2 ledger2 nameCert2 =>
            cases h
            rfl

instance ratClassifierTransportSealNontrivial :
    Nontrivial RatClassifierTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RatClassifierTransportSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RatClassifierTransportSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RatClassifierTransportSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ratClassifierTransportSealChapterTasteGate

theorem RatClassifierTransportSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      ratClassifierTransportSealDecodeBHist (ratClassifierTransportSealEncodeBHist h) = h) ∧
      (∀ x : RatClassifierTransportSealUp,
        ratClassifierTransportSealFromEventFlow
          (ratClassifierTransportSealToEventFlow x) = some x) ∧
        (∀ x y : RatClassifierTransportSealUp,
          ratClassifierTransportSealToEventFlow x =
            ratClassifierTransportSealToEventFlow y → x = y) ∧
          ratClassifierTransportSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ratClassifierTransportSeal_decode_encode_bhist,
      ratClassifierTransportSeal_round_trip,
      by
        intro x y heq
        exact ratClassifierTransportSealToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RatClassifierTransportSealUp
