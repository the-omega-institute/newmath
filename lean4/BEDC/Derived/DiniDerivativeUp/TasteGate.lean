import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniDerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniDerivativeUp : Type where
  | mk (X F Q S B R W H C P N : BHist) : DiniDerivativeUp
  deriving DecidableEq

def diniDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniDerivativeEncodeBHist h

def diniDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniDerivativeDecodeBHist tail)

private theorem diniDerivative_decode_encode_bhist :
    ∀ h : BHist, diniDerivativeDecodeBHist (diniDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diniDerivativeFields : DiniDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniDerivativeUp.mk X F Q S B R W H C P N => [X, F, Q, S, B, R, W, H, C, P, N]

def diniDerivativeToEventFlow : DiniDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diniDerivativeFields x).map diniDerivativeEncodeBHist

private def diniDerivativeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diniDerivativeRawAt index rest

private def diniDerivativeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => diniDerivativeLengthEq index rest

def diniDerivativeFromEventFlow : EventFlow → Option DiniDerivativeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match diniDerivativeLengthEq 11 flow with
      | true =>
          some
            (DiniDerivativeUp.mk
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 0 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 1 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 2 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 3 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 4 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 5 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 6 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 7 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 8 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 9 flow))
              (diniDerivativeDecodeBHist (diniDerivativeRawAt 10 flow)))
      | false => none

private theorem diniDerivative_round_trip :
    ∀ x : DiniDerivativeUp,
      diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F Q S B R W H C P N =>
      change
        some
          (DiniDerivativeUp.mk
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist X))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist F))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist Q))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist S))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist B))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist R))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist W))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist H))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist C))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist P))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist N))) =
          some (DiniDerivativeUp.mk X F Q S B R W H C P N)
      rw [diniDerivative_decode_encode_bhist X, diniDerivative_decode_encode_bhist F,
        diniDerivative_decode_encode_bhist Q, diniDerivative_decode_encode_bhist S,
        diniDerivative_decode_encode_bhist B, diniDerivative_decode_encode_bhist R,
        diniDerivative_decode_encode_bhist W, diniDerivative_decode_encode_bhist H,
        diniDerivative_decode_encode_bhist C, diniDerivative_decode_encode_bhist P,
        diniDerivative_decode_encode_bhist N]

private theorem diniDerivativeToEventFlow_injective {x y : DiniDerivativeUp} :
    diniDerivativeToEventFlow x = diniDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) =
        diniDerivativeFromEventFlow (diniDerivativeToEventFlow y) :=
    congrArg diniDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diniDerivative_round_trip x).symm
      (Eq.trans hread (diniDerivative_round_trip y)))

instance diniDerivativeBHistCarrier : BHistCarrier DiniDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniDerivativeToEventFlow
  fromEventFlow := diniDerivativeFromEventFlow

instance diniDerivativeChapterTasteGate : ChapterTasteGate DiniDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) = some x
    exact diniDerivative_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diniDerivativeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DiniDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diniDerivativeChapterTasteGate

theorem DiniDerivativeTasteGate_single_carrier_alignment :
    (∀ h : BHist, diniDerivativeDecodeBHist (diniDerivativeEncodeBHist h) = h) ∧
      (∀ x : DiniDerivativeUp,
        diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) = some x) ∧
      (∀ x y : DiniDerivativeUp,
        diniDerivativeToEventFlow x = diniDerivativeToEventFlow y → x = y) ∧
      diniDerivativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨diniDerivative_decode_encode_bhist,
      diniDerivative_round_trip,
      (fun _ _ heq => diniDerivativeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DiniDerivativeUp
