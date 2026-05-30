import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAverageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAverageUp : Type where
  | mk (I R W D B S K M E H C P N : BHist) : RegularCauchyAverageUp
  deriving DecidableEq

def regularCauchyAverageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAverageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAverageEncodeBHist h

def regularCauchyAverageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAverageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAverageDecodeBHist tail)

private theorem regularCauchyAverage_decode_encode_bhist :
    ∀ h : BHist, regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyAverageFields : RegularCauchyAverageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAverageUp.mk I R W D B S K M E H C P N =>
      [I, R, W, D, B, S, K, M, E, H, C, P, N]

def regularCauchyAverageToEventFlow : RegularCauchyAverageUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyAverageFields x).map regularCauchyAverageEncodeBHist

private def regularCauchyAverageEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyAverageEventAtDefault index rest

def regularCauchyAverageFromEventFlow (ef : EventFlow) : Option RegularCauchyAverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyAverageUp.mk
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 0 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 1 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 2 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 3 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 4 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 5 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 6 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 7 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 8 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 9 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 10 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 11 ef))
      (regularCauchyAverageDecodeBHist (regularCauchyAverageEventAtDefault 12 ef)))

private theorem regularCauchyAverage_round_trip :
    ∀ x : RegularCauchyAverageUp,
      regularCauchyAverageFromEventFlow (regularCauchyAverageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I R W D B S K M E H C P N =>
      change
        some
          (RegularCauchyAverageUp.mk
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist I))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist R))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist W))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist D))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist B))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist S))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist K))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist M))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist E))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist H))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist C))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist P))
            (regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist N))) =
          some (RegularCauchyAverageUp.mk I R W D B S K M E H C P N)
      rw [regularCauchyAverage_decode_encode_bhist I,
        regularCauchyAverage_decode_encode_bhist R,
        regularCauchyAverage_decode_encode_bhist W,
        regularCauchyAverage_decode_encode_bhist D,
        regularCauchyAverage_decode_encode_bhist B,
        regularCauchyAverage_decode_encode_bhist S,
        regularCauchyAverage_decode_encode_bhist K,
        regularCauchyAverage_decode_encode_bhist M,
        regularCauchyAverage_decode_encode_bhist E,
        regularCauchyAverage_decode_encode_bhist H,
        regularCauchyAverage_decode_encode_bhist C,
        regularCauchyAverage_decode_encode_bhist P,
        regularCauchyAverage_decode_encode_bhist N]

private theorem regularCauchyAverageToEventFlow_injective {x y : RegularCauchyAverageUp} :
    regularCauchyAverageToEventFlow x = regularCauchyAverageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyAverageFromEventFlow (regularCauchyAverageToEventFlow x) =
        regularCauchyAverageFromEventFlow (regularCauchyAverageToEventFlow y) :=
    congrArg regularCauchyAverageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyAverage_round_trip x).symm
      (Eq.trans hread (regularCauchyAverage_round_trip y)))

instance regularCauchyAverageBHistCarrier : BHistCarrier RegularCauchyAverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAverageToEventFlow
  fromEventFlow := regularCauchyAverageFromEventFlow

instance regularCauchyAverageChapterTasteGate : ChapterTasteGate RegularCauchyAverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyAverageFromEventFlow (regularCauchyAverageToEventFlow x) = some x
    exact regularCauchyAverage_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyAverageToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyAverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyAverageChapterTasteGate

theorem RegularCauchyAverageTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyAverageDecodeBHist (regularCauchyAverageEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyAverageUp,
        regularCauchyAverageFromEventFlow (regularCauchyAverageToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyAverageUp,
          regularCauchyAverageToEventFlow x = regularCauchyAverageToEventFlow y → x = y) ∧
          regularCauchyAverageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyAverage_decode_encode_bhist,
      regularCauchyAverage_round_trip,
      (fun _ _ heq => regularCauchyAverageToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyAverageUp
