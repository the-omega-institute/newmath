import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungIntegralUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungIntegralUp : Type where
  | mk (F G V C S D R E H K P N : BHist) : YoungIntegralUp
  deriving DecidableEq

def youngIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngIntegralEncodeBHist h

def youngIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngIntegralDecodeBHist tail)

private theorem youngIntegral_decode_encode :
    ∀ h : BHist, youngIntegralDecodeBHist (youngIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngIntegralFields : YoungIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungIntegralUp.mk F G V C S D R E H K P N => [F, G, V, C, S, D, R, E, H, K, P, N]

def youngIntegralToEventFlow : YoungIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map youngIntegralEncodeBHist (youngIntegralFields x)

private def youngIntegralRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => youngIntegralRawAt index rest

def youngIntegralFromEventFlow (flow : EventFlow) : Option YoungIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (YoungIntegralUp.mk
      (youngIntegralDecodeBHist (youngIntegralRawAt 0 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 1 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 2 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 3 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 4 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 5 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 6 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 7 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 8 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 9 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 10 flow))
      (youngIntegralDecodeBHist (youngIntegralRawAt 11 flow)))

private theorem youngIntegral_round_trip :
    ∀ x : YoungIntegralUp,
      youngIntegralFromEventFlow (youngIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G V C S D R E H K P N =>
      change
        some
          (YoungIntegralUp.mk
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist F))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist G))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist V))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist C))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist S))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist D))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist R))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist E))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist H))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist K))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist P))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist N))) =
          some (YoungIntegralUp.mk F G V C S D R E H K P N)
      rw [youngIntegral_decode_encode F, youngIntegral_decode_encode G,
        youngIntegral_decode_encode V, youngIntegral_decode_encode C,
        youngIntegral_decode_encode S, youngIntegral_decode_encode D,
        youngIntegral_decode_encode R, youngIntegral_decode_encode E,
        youngIntegral_decode_encode H, youngIntegral_decode_encode K,
        youngIntegral_decode_encode P, youngIntegral_decode_encode N]

private theorem youngIntegralToEventFlow_injective {x y : YoungIntegralUp} :
    youngIntegralToEventFlow x = youngIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngIntegralFromEventFlow (youngIntegralToEventFlow x) =
        youngIntegralFromEventFlow (youngIntegralToEventFlow y) :=
    congrArg youngIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (youngIntegral_round_trip x).symm
      (Eq.trans hread (youngIntegral_round_trip y)))

instance youngIntegralBHistCarrier : BHistCarrier YoungIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngIntegralToEventFlow
  fromEventFlow := youngIntegralFromEventFlow

instance youngIntegralChapterTasteGate : ChapterTasteGate YoungIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngIntegralFromEventFlow (youngIntegralToEventFlow x) = some x
    exact youngIntegral_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (youngIntegralToEventFlow_injective heq)

def taste_gate : ChapterTasteGate YoungIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  youngIntegralChapterTasteGate

theorem YoungIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist, youngIntegralDecodeBHist (youngIntegralEncodeBHist h) = h) ∧
      youngIntegralFields
          (YoungIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact youngIntegral_decode_encode
  · rfl

end BEDC.Derived.YoungIntegralUp.TasteGate
