import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyInterpolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyInterpolationUp : Type where
  | mk (R D M W S E H C P N : BHist) : RegularCauchyInterpolationUp
  deriving DecidableEq

def regularCauchyInterpolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyInterpolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyInterpolationEncodeBHist h

def regularCauchyInterpolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyInterpolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyInterpolationDecodeBHist tail)

private theorem regularCauchyInterpolation_decode_encode :
    ∀ h : BHist,
      regularCauchyInterpolationDecodeBHist
          (regularCauchyInterpolationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyInterpolationFields :
    RegularCauchyInterpolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyInterpolationUp.mk R D M W S E H C P N =>
      [R, D, M, W, S, E, H, C, P, N]

def regularCauchyInterpolationToEventFlow :
    RegularCauchyInterpolationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyInterpolationEncodeBHist
        (regularCauchyInterpolationFields x)

private def regularCauchyInterpolationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyInterpolationRawAt index rest

def regularCauchyInterpolationFromEventFlow
    (flow : EventFlow) : Option RegularCauchyInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyInterpolationUp.mk
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 0 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 1 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 2 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 3 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 4 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 5 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 6 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 7 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 8 flow))
      (regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationRawAt 9 flow)))

private theorem regularCauchyInterpolation_round_trip :
    ∀ x : RegularCauchyInterpolationUp,
      regularCauchyInterpolationFromEventFlow
          (regularCauchyInterpolationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R D M W S E H C P N =>
      change
        some
          (RegularCauchyInterpolationUp.mk
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist R))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist D))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist M))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist W))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist S))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist E))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist H))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist C))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist P))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist N))) =
          some (RegularCauchyInterpolationUp.mk R D M W S E H C P N)
      rw [regularCauchyInterpolation_decode_encode R,
        regularCauchyInterpolation_decode_encode D,
        regularCauchyInterpolation_decode_encode M,
        regularCauchyInterpolation_decode_encode W,
        regularCauchyInterpolation_decode_encode S,
        regularCauchyInterpolation_decode_encode E,
        regularCauchyInterpolation_decode_encode H,
        regularCauchyInterpolation_decode_encode C,
        regularCauchyInterpolation_decode_encode P,
        regularCauchyInterpolation_decode_encode N]

private theorem regularCauchyInterpolationToEventFlow_injective
    {x y : RegularCauchyInterpolationUp} :
    regularCauchyInterpolationToEventFlow x =
        regularCauchyInterpolationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyInterpolationFromEventFlow
          (regularCauchyInterpolationToEventFlow x) =
        regularCauchyInterpolationFromEventFlow
          (regularCauchyInterpolationToEventFlow y) :=
    congrArg regularCauchyInterpolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyInterpolation_round_trip x).symm
      (Eq.trans hread (regularCauchyInterpolation_round_trip y)))

instance regularCauchyInterpolationBHistCarrier :
    BHistCarrier RegularCauchyInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyInterpolationToEventFlow
  fromEventFlow := regularCauchyInterpolationFromEventFlow

instance regularCauchyInterpolationChapterTasteGate :
    ChapterTasteGate RegularCauchyInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyInterpolationFromEventFlow
          (regularCauchyInterpolationToEventFlow x) =
        some x
    exact regularCauchyInterpolation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyInterpolationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyInterpolationChapterTasteGate

theorem RegularCauchyInterpolationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyInterpolationDecodeBHist
          (regularCauchyInterpolationEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyInterpolationUp,
        regularCauchyInterpolationFromEventFlow
            (regularCauchyInterpolationToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyInterpolationUp,
          regularCauchyInterpolationToEventFlow x =
              regularCauchyInterpolationToEventFlow y →
            x = y) ∧
          regularCauchyInterpolationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyInterpolation_decode_encode,
      regularCauchyInterpolation_round_trip,
      by
        intro x y heq
        exact regularCauchyInterpolationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyInterpolationUp
