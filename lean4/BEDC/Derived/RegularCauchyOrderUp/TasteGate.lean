import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyOrderUp : Type where
  | mk (X Y S D R L A H C P N : BHist) : RegularCauchyOrderUp
  deriving DecidableEq

def regularCauchyOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyOrderEncodeBHist h

def regularCauchyOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyOrderDecodeBHist tail)

private theorem regularCauchyOrder_decode_encode :
    ∀ h : BHist, regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyOrderFields : RegularCauchyOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyOrderUp.mk X Y S D R L A H C P N => [X, Y, S, D, R, L, A, H, C, P, N]

def regularCauchyOrderToEventFlow : RegularCauchyOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regularCauchyOrderEncodeBHist (regularCauchyOrderFields x)

private def regularCauchyOrderRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyOrderRawAt index rest

def regularCauchyOrderFromEventFlow (flow : EventFlow) : Option RegularCauchyOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyOrderUp.mk
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 0 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 1 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 2 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 3 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 4 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 5 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 6 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 7 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 8 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 9 flow))
      (regularCauchyOrderDecodeBHist (regularCauchyOrderRawAt 10 flow)))

private theorem regularCauchyOrder_round_trip :
    ∀ x : RegularCauchyOrderUp,
      regularCauchyOrderFromEventFlow (regularCauchyOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S D R L A H C P N =>
      change
        some
          (RegularCauchyOrderUp.mk
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist X))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist Y))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist S))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist D))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist R))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist L))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist A))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist H))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist C))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist P))
            (regularCauchyOrderDecodeBHist (regularCauchyOrderEncodeBHist N))) =
          some (RegularCauchyOrderUp.mk X Y S D R L A H C P N)
      rw [regularCauchyOrder_decode_encode X,
        regularCauchyOrder_decode_encode Y,
        regularCauchyOrder_decode_encode S,
        regularCauchyOrder_decode_encode D,
        regularCauchyOrder_decode_encode R,
        regularCauchyOrder_decode_encode L,
        regularCauchyOrder_decode_encode A,
        regularCauchyOrder_decode_encode H,
        regularCauchyOrder_decode_encode C,
        regularCauchyOrder_decode_encode P,
        regularCauchyOrder_decode_encode N]

private theorem regularCauchyOrderToEventFlow_injective {x y : RegularCauchyOrderUp} :
    regularCauchyOrderToEventFlow x = regularCauchyOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyOrderFromEventFlow (regularCauchyOrderToEventFlow x) =
        regularCauchyOrderFromEventFlow (regularCauchyOrderToEventFlow y) :=
    congrArg regularCauchyOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyOrder_round_trip x).symm
      (Eq.trans hread (regularCauchyOrder_round_trip y)))

instance regularCauchyOrderBHistCarrier : BHistCarrier RegularCauchyOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyOrderToEventFlow
  fromEventFlow := regularCauchyOrderFromEventFlow

instance regularCauchyOrderChapterTasteGate : ChapterTasteGate RegularCauchyOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyOrderFromEventFlow (regularCauchyOrderToEventFlow x) = some x
    exact regularCauchyOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyOrderToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyOrderChapterTasteGate

theorem RegularCauchyOrderTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyOrderUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact regularCauchyOrderChapterTasteGate

end BEDC.Derived.RegularCauchyOrderUp
