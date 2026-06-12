import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLocatedApartnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLocatedApartnessUp : Type where
  | mk (Q A B S R D E H C P N : BHist) : CauchyLocatedApartnessUp
  deriving DecidableEq

def cauchyLocatedApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyLocatedApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyLocatedApartnessEncodeBHist h

def cauchyLocatedApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLocatedApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLocatedApartnessDecodeBHist tail)

private theorem cauchyLocatedApartness_decode_encode :
    ∀ h : BHist, cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyLocatedApartnessFields : CauchyLocatedApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyLocatedApartnessUp.mk Q A B S R D E H C P N => [Q, A, B, S, R, D, E, H, C, P, N]

def cauchyLocatedApartnessToEventFlow : CauchyLocatedApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (cauchyLocatedApartnessFields token).map cauchyLocatedApartnessEncodeBHist

private def cauchyLocatedApartnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyLocatedApartnessEventAt index rest

def cauchyLocatedApartnessFromEventFlow
    (flow : EventFlow) : Option CauchyLocatedApartnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyLocatedApartnessUp.mk
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 0 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 1 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 2 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 3 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 4 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 5 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 6 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 7 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 8 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 9 flow))
      (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEventAt 10 flow)))

private theorem cauchyLocatedApartness_round_trip :
    ∀ x : CauchyLocatedApartnessUp,
      cauchyLocatedApartnessFromEventFlow (cauchyLocatedApartnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A B S R D E H C P N =>
      change
        some
            (CauchyLocatedApartnessUp.mk
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist Q))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist A))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist B))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist S))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist R))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist D))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist E))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist H))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist C))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist P))
              (cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist N))) =
          some (CauchyLocatedApartnessUp.mk Q A B S R D E H C P N)
      rw [cauchyLocatedApartness_decode_encode Q, cauchyLocatedApartness_decode_encode A,
        cauchyLocatedApartness_decode_encode B, cauchyLocatedApartness_decode_encode S,
        cauchyLocatedApartness_decode_encode R, cauchyLocatedApartness_decode_encode D,
        cauchyLocatedApartness_decode_encode E, cauchyLocatedApartness_decode_encode H,
        cauchyLocatedApartness_decode_encode C, cauchyLocatedApartness_decode_encode P,
        cauchyLocatedApartness_decode_encode N]

private theorem cauchyLocatedApartnessToEventFlow_injective
    {x y : CauchyLocatedApartnessUp} :
    cauchyLocatedApartnessToEventFlow x = cauchyLocatedApartnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyLocatedApartnessFromEventFlow (cauchyLocatedApartnessToEventFlow x) =
        cauchyLocatedApartnessFromEventFlow (cauchyLocatedApartnessToEventFlow y) :=
    congrArg cauchyLocatedApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyLocatedApartness_round_trip x).symm
      (Eq.trans hread (cauchyLocatedApartness_round_trip y)))

instance cauchyLocatedApartnessBHistCarrier : BHistCarrier CauchyLocatedApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyLocatedApartnessToEventFlow
  fromEventFlow := cauchyLocatedApartnessFromEventFlow

instance cauchyLocatedApartnessChapterTasteGate :
    ChapterTasteGate CauchyLocatedApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyLocatedApartnessFromEventFlow (cauchyLocatedApartnessToEventFlow x) =
        some x
    exact cauchyLocatedApartness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyLocatedApartnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyLocatedApartnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyLocatedApartnessChapterTasteGate

theorem CauchyLocatedApartnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyLocatedApartnessDecodeBHist (cauchyLocatedApartnessEncodeBHist h) = h) ∧
      (∀ x : CauchyLocatedApartnessUp,
        cauchyLocatedApartnessFromEventFlow (cauchyLocatedApartnessToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyLocatedApartnessUp,
          cauchyLocatedApartnessToEventFlow x = cauchyLocatedApartnessToEventFlow y →
            x = y) ∧
          cauchyLocatedApartnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyLocatedApartness_decode_encode, cauchyLocatedApartness_round_trip,
      fun _x _y heq => cauchyLocatedApartnessToEventFlow_injective heq, rfl⟩

end BEDC.Derived.CauchyLocatedApartnessUp
