import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalDiagonalSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalDiagonalSealUp : Type where
  | mk :
      (precision cofinalTail diagonalBudget diagonalLimit regularSource streamWindow
        dyadicLedger realSeal transport replay provenance nameCert : BHist) →
        CofinalDiagonalSealUp
  deriving DecidableEq

def cofinalDiagonalSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalDiagonalSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalDiagonalSealEncodeBHist h

def cofinalDiagonalSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalDiagonalSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalDiagonalSealDecodeBHist tail)

private theorem cofinalDiagonalSeal_decode_encode_bhist :
    ∀ h : BHist, cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalDiagonalSealToEventFlow : CofinalDiagonalSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalDiagonalSealUp.mk precision cofinalTail diagonalBudget diagonalLimit regularSource
      streamWindow dyadicLedger realSeal transport replay provenance nameCert =>
      [[BMark.b0],
        cofinalDiagonalSealEncodeBHist precision,
        [BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist cofinalTail,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist diagonalBudget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist diagonalLimit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist regularSource,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalDiagonalSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist nameCert]

private def cofinalDiagonalSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cofinalDiagonalSealRawAt n rest

private def cofinalDiagonalSealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cofinalDiagonalSealLengthEq n rest

def cofinalDiagonalSealFromEventFlow :
    EventFlow → Option CofinalDiagonalSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cofinalDiagonalSealLengthEq 24 flow with
      | true =>
          some
            (CofinalDiagonalSealUp.mk
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 1 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 3 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 5 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 7 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 9 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 11 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 13 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 15 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 17 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 19 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 21 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 23 flow)))
      | false => none

private theorem cofinalDiagonalSeal_round_trip :
    ∀ x : CofinalDiagonalSealUp,
      cofinalDiagonalSealFromEventFlow
        (cofinalDiagonalSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision cofinalTail diagonalBudget diagonalLimit regularSource streamWindow
      dyadicLedger realSeal transport replay provenance nameCert =>
      change
        some
          (CofinalDiagonalSealUp.mk
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist precision))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist cofinalTail))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist diagonalBudget))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist diagonalLimit))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist regularSource))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist streamWindow))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist dyadicLedger))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist realSeal))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist transport))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist replay))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist provenance))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist nameCert))) =
          some
            (CofinalDiagonalSealUp.mk precision cofinalTail diagonalBudget diagonalLimit
              regularSource streamWindow dyadicLedger realSeal transport replay provenance
              nameCert)
      rw [cofinalDiagonalSeal_decode_encode_bhist precision,
        cofinalDiagonalSeal_decode_encode_bhist cofinalTail,
        cofinalDiagonalSeal_decode_encode_bhist diagonalBudget,
        cofinalDiagonalSeal_decode_encode_bhist diagonalLimit,
        cofinalDiagonalSeal_decode_encode_bhist regularSource,
        cofinalDiagonalSeal_decode_encode_bhist streamWindow,
        cofinalDiagonalSeal_decode_encode_bhist dyadicLedger,
        cofinalDiagonalSeal_decode_encode_bhist realSeal,
        cofinalDiagonalSeal_decode_encode_bhist transport,
        cofinalDiagonalSeal_decode_encode_bhist replay,
        cofinalDiagonalSeal_decode_encode_bhist provenance,
        cofinalDiagonalSeal_decode_encode_bhist nameCert]

private theorem cofinalDiagonalSealToEventFlow_injective
    {x y : CofinalDiagonalSealUp} :
    cofinalDiagonalSealToEventFlow x = cofinalDiagonalSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow x) =
        cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow y) :=
    congrArg cofinalDiagonalSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalDiagonalSeal_round_trip x).symm
      (Eq.trans hread (cofinalDiagonalSeal_round_trip y)))

instance cofinalDiagonalSealBHistCarrier :
    BHistCarrier CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalDiagonalSealToEventFlow
  fromEventFlow := cofinalDiagonalSealFromEventFlow

instance cofinalDiagonalSealChapterTasteGate :
    ChapterTasteGate CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalDiagonalSealFromEventFlow
        (cofinalDiagonalSealToEventFlow x) = some x
    exact cofinalDiagonalSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalDiagonalSealToEventFlow_injective heq)

instance cofinalDiagonalSealFieldFaithful :
    FieldFaithful CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CofinalDiagonalSealUp.mk precision cofinalTail diagonalBudget diagonalLimit regularSource
        streamWindow dyadicLedger realSeal transport replay provenance nameCert =>
        [precision, cofinalTail, diagonalBudget, diagonalLimit, regularSource, streamWindow,
          dyadicLedger, realSeal, transport, replay, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk precision1 cofinalTail1 diagonalBudget1 diagonalLimit1 regularSource1 streamWindow1
        dyadicLedger1 realSeal1 transport1 replay1 provenance1 nameCert1 =>
        cases y with
        | mk precision2 cofinalTail2 diagonalBudget2 diagonalLimit2 regularSource2
            streamWindow2 dyadicLedger2 realSeal2 transport2 replay2 provenance2 nameCert2 =>
            cases hfields
            rfl

instance cofinalDiagonalSealNontrivial :
    Nontrivial CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalDiagonalSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalDiagonalSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CofinalDiagonalSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalDiagonalSealChapterTasteGate

theorem CofinalDiagonalSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist h) = h) ∧
      (∀ x : CofinalDiagonalSealUp,
        cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow x) = some x) ∧
        (∀ x y : CofinalDiagonalSealUp,
          cofinalDiagonalSealToEventFlow x = cofinalDiagonalSealToEventFlow y → x = y) ∧
          cofinalDiagonalSealEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : CofinalDiagonalSealUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cofinalDiagonalSeal_decode_encode_bhist,
      cofinalDiagonalSeal_round_trip,
      by
        intro x y heq
        exact cofinalDiagonalSealToEventFlow_injective heq,
      rfl,
      ⟨CofinalDiagonalSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        CofinalDiagonalSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.CofinalDiagonalSealUp
