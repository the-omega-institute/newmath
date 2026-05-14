import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaCriticalPairUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaCriticalPairUp : Type where
  | mk :
      (overlap leftBranch rightBranch commonReduct boundary transport route provenance
        nameCert : BHist) →
        BetaCriticalPairUp
  deriving DecidableEq

def betaCriticalPairEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaCriticalPairEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaCriticalPairEncodeBHist h

def betaCriticalPairDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaCriticalPairDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaCriticalPairDecodeBHist tail)

private theorem betaCriticalPair_decode_encode_bhist :
    ∀ h : BHist, betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def betaCriticalPairToEventFlow : BetaCriticalPairUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaCriticalPairUp.mk overlap leftBranch rightBranch commonReduct boundary transport route
      provenance nameCert =>
      [[BMark.b0],
        betaCriticalPairEncodeBHist overlap,
        [BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist leftBranch,
        [BMark.b1, BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist rightBranch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist commonReduct,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        betaCriticalPairEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        betaCriticalPairEncodeBHist nameCert]

private def betaCriticalPairRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => betaCriticalPairRawAt n rest

private def betaCriticalPairLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => betaCriticalPairLengthEq n rest

def betaCriticalPairFromEventFlow : EventFlow → Option BetaCriticalPairUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match betaCriticalPairLengthEq 18 flow with
      | true =>
          some
            (BetaCriticalPairUp.mk
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 1 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 3 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 5 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 7 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 9 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 11 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 13 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 15 flow))
              (betaCriticalPairDecodeBHist (betaCriticalPairRawAt 17 flow)))
      | false => none

private theorem betaCriticalPair_round_trip :
    ∀ x : BetaCriticalPairUp,
      betaCriticalPairFromEventFlow (betaCriticalPairToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk overlap leftBranch rightBranch commonReduct boundary transport route provenance nameCert =>
      change
        some
          (BetaCriticalPairUp.mk
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist overlap))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist leftBranch))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist rightBranch))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist commonReduct))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist boundary))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist transport))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist route))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist provenance))
            (betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist nameCert))) =
          some
            (BetaCriticalPairUp.mk overlap leftBranch rightBranch commonReduct boundary
              transport route provenance nameCert)
      rw [betaCriticalPair_decode_encode_bhist overlap,
        betaCriticalPair_decode_encode_bhist leftBranch,
        betaCriticalPair_decode_encode_bhist rightBranch,
        betaCriticalPair_decode_encode_bhist commonReduct,
        betaCriticalPair_decode_encode_bhist boundary,
        betaCriticalPair_decode_encode_bhist transport,
        betaCriticalPair_decode_encode_bhist route,
        betaCriticalPair_decode_encode_bhist provenance,
        betaCriticalPair_decode_encode_bhist nameCert]

private theorem betaCriticalPairToEventFlow_injective {x y : BetaCriticalPairUp} :
    betaCriticalPairToEventFlow x = betaCriticalPairToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      betaCriticalPairFromEventFlow (betaCriticalPairToEventFlow x) =
        betaCriticalPairFromEventFlow (betaCriticalPairToEventFlow y) :=
    congrArg betaCriticalPairFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (betaCriticalPair_round_trip x).symm
      (Eq.trans hread (betaCriticalPair_round_trip y)))

instance betaCriticalPairBHistCarrier : BHistCarrier BetaCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaCriticalPairToEventFlow
  fromEventFlow := betaCriticalPairFromEventFlow

instance betaCriticalPairChapterTasteGate : ChapterTasteGate BetaCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change betaCriticalPairFromEventFlow (betaCriticalPairToEventFlow x) = some x
    exact betaCriticalPair_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaCriticalPairToEventFlow_injective heq)

instance betaCriticalPairFieldFaithful : FieldFaithful BetaCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BetaCriticalPairUp.mk overlap leftBranch rightBranch commonReduct boundary transport route
        provenance nameCert =>
        [overlap, leftBranch, rightBranch, commonReduct, boundary, transport, route,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk overlap1 leftBranch1 rightBranch1 commonReduct1 boundary1 transport1 route1
        provenance1 nameCert1 =>
        cases y with
        | mk overlap2 leftBranch2 rightBranch2 commonReduct2 boundary2 transport2 route2
            provenance2 nameCert2 =>
            cases h
            rfl

instance betaCriticalPairNontrivial : Nontrivial BetaCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BetaCriticalPairUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BetaCriticalPairUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BetaCriticalPairUp :=
  -- BEDC touchpoint anchor: BHist BMark
  betaCriticalPairChapterTasteGate

theorem BetaCriticalPairTasteGate_single_carrier_alignment :
    (∀ h : BHist, betaCriticalPairDecodeBHist (betaCriticalPairEncodeBHist h) = h) ∧
      (∀ x : BetaCriticalPairUp,
        betaCriticalPairFromEventFlow (betaCriticalPairToEventFlow x) = some x) ∧
        (∀ x y : BetaCriticalPairUp,
          betaCriticalPairToEventFlow x = betaCriticalPairToEventFlow y → x = y) ∧
          betaCriticalPairEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨betaCriticalPair_decode_encode_bhist,
      betaCriticalPair_round_trip,
      by
        intro x y heq
        exact betaCriticalPairToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BetaCriticalPairUp
