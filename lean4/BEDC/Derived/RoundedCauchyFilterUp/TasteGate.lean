import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RoundedCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoundedCauchyFilterUp : Type where
  | mk (B F R U W Q D E H C P N : BHist) : RoundedCauchyFilterUp

def roundedCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roundedCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roundedCauchyFilterEncodeBHist h

def roundedCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roundedCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roundedCauchyFilterDecodeBHist tail)

private theorem roundedCauchyFilter_decode_encode_bhist :
    ∀ h : BHist,
      roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def roundedCauchyFilterFields : RoundedCauchyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoundedCauchyFilterUp.mk B F R U W Q D E H C P N =>
      [B, F, R, U, W, Q, D, E, H, C, P, N]

def roundedCauchyFilterToEventFlow : RoundedCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (roundedCauchyFilterFields x).map roundedCauchyFilterEncodeBHist

private def roundedCauchyFilterRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => roundedCauchyFilterRawAt n rest

private def roundedCauchyFilterLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => roundedCauchyFilterLengthEq n rest

def roundedCauchyFilterFromEventFlow : EventFlow → Option RoundedCauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match roundedCauchyFilterLengthEq 12 flow with
      | true =>
          some
            (RoundedCauchyFilterUp.mk
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 0 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 1 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 2 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 3 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 4 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 5 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 6 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 7 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 8 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 9 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 10 flow))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterRawAt 11 flow)))
      | false => none

private theorem roundedCauchyFilter_round_trip :
    ∀ x : RoundedCauchyFilterUp,
      roundedCauchyFilterFromEventFlow (roundedCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F R U W Q D E H C P N =>
      change
        some
            (RoundedCauchyFilterUp.mk
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist B))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist F))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist R))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist U))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist W))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist Q))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist D))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist E))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist H))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist C))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist P))
              (roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist N))) =
          some (RoundedCauchyFilterUp.mk B F R U W Q D E H C P N)
      rw [roundedCauchyFilter_decode_encode_bhist B,
        roundedCauchyFilter_decode_encode_bhist F,
        roundedCauchyFilter_decode_encode_bhist R,
        roundedCauchyFilter_decode_encode_bhist U,
        roundedCauchyFilter_decode_encode_bhist W,
        roundedCauchyFilter_decode_encode_bhist Q,
        roundedCauchyFilter_decode_encode_bhist D,
        roundedCauchyFilter_decode_encode_bhist E,
        roundedCauchyFilter_decode_encode_bhist H,
        roundedCauchyFilter_decode_encode_bhist C,
        roundedCauchyFilter_decode_encode_bhist P,
        roundedCauchyFilter_decode_encode_bhist N]

private theorem roundedCauchyFilterToEventFlow_injective {x y : RoundedCauchyFilterUp} :
    roundedCauchyFilterToEventFlow x = roundedCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roundedCauchyFilterFromEventFlow (roundedCauchyFilterToEventFlow x) =
        roundedCauchyFilterFromEventFlow (roundedCauchyFilterToEventFlow y) :=
    congrArg roundedCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (roundedCauchyFilter_round_trip x).symm
      (Eq.trans hread (roundedCauchyFilter_round_trip y)))

instance roundedCauchyFilterBHistCarrier : BHistCarrier RoundedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roundedCauchyFilterToEventFlow
  fromEventFlow := roundedCauchyFilterFromEventFlow

instance roundedCauchyFilterChapterTasteGate : ChapterTasteGate RoundedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roundedCauchyFilterFromEventFlow (roundedCauchyFilterToEventFlow x) = some x
    exact roundedCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (roundedCauchyFilterToEventFlow_injective heq)

theorem RoundedCauchyFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, roundedCauchyFilterDecodeBHist (roundedCauchyFilterEncodeBHist h) = h) ∧
      (∀ x : RoundedCauchyFilterUp,
        roundedCauchyFilterFromEventFlow (roundedCauchyFilterToEventFlow x) = some x) ∧
      (∀ x y : RoundedCauchyFilterUp,
        roundedCauchyFilterToEventFlow x = roundedCauchyFilterToEventFlow y → x = y) ∧
      roundedCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨roundedCauchyFilter_decode_encode_bhist, roundedCauchyFilter_round_trip,
      (fun _ _ heq => roundedCauchyFilterToEventFlow_injective heq), rfl⟩

end BEDC.Derived.RoundedCauchyFilterUp
