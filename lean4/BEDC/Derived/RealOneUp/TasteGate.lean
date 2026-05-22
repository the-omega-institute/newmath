import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealOneUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealOneUp : Type where
  | mk (q S R D E H C P N : BHist) : RealOneUp
  deriving DecidableEq

def realOneEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realOneEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realOneEncodeBHist h

def realOneDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realOneDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realOneDecodeBHist tail)

private theorem realOne_decode_encode_bhist :
    ∀ h : BHist, realOneDecodeBHist (realOneEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realOneFields : RealOneUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealOneUp.mk q S R D E H C P N => [q, S, R, D, E, H, C, P, N]

def realOneToEventFlow : RealOneUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realOneFields x).map realOneEncodeBHist

private def realOneEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realOneEventAtDefault index rest

def realOneFromEventFlow (flow : EventFlow) : Option RealOneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealOneUp.mk
      (realOneDecodeBHist (realOneEventAtDefault 0 flow))
      (realOneDecodeBHist (realOneEventAtDefault 1 flow))
      (realOneDecodeBHist (realOneEventAtDefault 2 flow))
      (realOneDecodeBHist (realOneEventAtDefault 3 flow))
      (realOneDecodeBHist (realOneEventAtDefault 4 flow))
      (realOneDecodeBHist (realOneEventAtDefault 5 flow))
      (realOneDecodeBHist (realOneEventAtDefault 6 flow))
      (realOneDecodeBHist (realOneEventAtDefault 7 flow))
      (realOneDecodeBHist (realOneEventAtDefault 8 flow)))

private theorem realOne_round_trip :
    ∀ x : RealOneUp, realOneFromEventFlow (realOneToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q S R D E H C P N =>
      change
        some
          (RealOneUp.mk
            (realOneDecodeBHist (realOneEncodeBHist q))
            (realOneDecodeBHist (realOneEncodeBHist S))
            (realOneDecodeBHist (realOneEncodeBHist R))
            (realOneDecodeBHist (realOneEncodeBHist D))
            (realOneDecodeBHist (realOneEncodeBHist E))
            (realOneDecodeBHist (realOneEncodeBHist H))
            (realOneDecodeBHist (realOneEncodeBHist C))
            (realOneDecodeBHist (realOneEncodeBHist P))
            (realOneDecodeBHist (realOneEncodeBHist N))) =
          some (RealOneUp.mk q S R D E H C P N)
      rw [realOne_decode_encode_bhist q, realOne_decode_encode_bhist S,
        realOne_decode_encode_bhist R, realOne_decode_encode_bhist D,
        realOne_decode_encode_bhist E, realOne_decode_encode_bhist H,
        realOne_decode_encode_bhist C, realOne_decode_encode_bhist P,
        realOne_decode_encode_bhist N]

private theorem RealOneToEventFlow_injective {x y : RealOneUp} :
    realOneToEventFlow x = realOneToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realOneFromEventFlow (realOneToEventFlow x) =
        realOneFromEventFlow (realOneToEventFlow y) :=
    congrArg realOneFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realOne_round_trip x).symm (Eq.trans hread (realOne_round_trip y)))

instance realOneBHistCarrier : BHistCarrier RealOneUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realOneToEventFlow
  fromEventFlow := realOneFromEventFlow

instance realOneChapterTasteGate : ChapterTasteGate RealOneUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realOneFromEventFlow (realOneToEventFlow x) = some x
    exact realOne_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealOneToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealOneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realOneChapterTasteGate

theorem RealOneTasteGate_single_carrier_alignment :
    (∀ h : BHist, realOneDecodeBHist (realOneEncodeBHist h) = h) ∧
      (∀ x : RealOneUp, realOneFromEventFlow (realOneToEventFlow x) = some x) ∧
        (∀ x y : RealOneUp, realOneToEventFlow x = realOneToEventFlow y → x = y) ∧
          realOneEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realOne_decode_encode_bhist, realOne_round_trip,
      (fun _ _ heq => RealOneToEventFlow_injective heq), rfl⟩

end BEDC.Derived.RealOneUp
