import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubtractionUp : Type where
  | mk (X Y G A W D E S H C P N : BHist) : RegularCauchySubtractionUp
  deriving DecidableEq

def regularCauchySubtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubtractionEncodeBHist h

def regularCauchySubtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubtractionDecodeBHist tail)

private theorem regularCauchySubtraction_decode_encode :
    ∀ h : BHist,
      regularCauchySubtractionDecodeBHist
          (regularCauchySubtractionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubtractionFields :
    RegularCauchySubtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubtractionUp.mk X Y G A W D E S H C P N =>
      [X, Y, G, A, W, D, E, S, H, C, P, N]

def regularCauchySubtractionToEventFlow :
    RegularCauchySubtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchySubtractionEncodeBHist
        (regularCauchySubtractionFields x)

private def regularCauchySubtractionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySubtractionRawAt index rest

def regularCauchySubtractionFromEventFlow
    (flow : EventFlow) : Option RegularCauchySubtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySubtractionUp.mk
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 0 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 1 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 2 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 3 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 4 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 5 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 6 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 7 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 8 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 9 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 10 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 11 flow)))

private theorem regularCauchySubtraction_round_trip :
    ∀ x : RegularCauchySubtractionUp,
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y G A W D E S H C P N =>
      change
        some
          (RegularCauchySubtractionUp.mk
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist X))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist Y))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist G))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist A))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist W))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist D))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist E))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist S))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist H))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist C))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist P))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist N))) =
          some (RegularCauchySubtractionUp.mk X Y G A W D E S H C P N)
      rw [regularCauchySubtraction_decode_encode X,
        regularCauchySubtraction_decode_encode Y,
        regularCauchySubtraction_decode_encode G,
        regularCauchySubtraction_decode_encode A,
        regularCauchySubtraction_decode_encode W,
        regularCauchySubtraction_decode_encode D,
        regularCauchySubtraction_decode_encode E,
        regularCauchySubtraction_decode_encode S,
        regularCauchySubtraction_decode_encode H,
        regularCauchySubtraction_decode_encode C,
        regularCauchySubtraction_decode_encode P,
        regularCauchySubtraction_decode_encode N]

private theorem regularCauchySubtractionToEventFlow_injective
    {x y : RegularCauchySubtractionUp} :
    regularCauchySubtractionToEventFlow x =
        regularCauchySubtractionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow y) :=
    congrArg regularCauchySubtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubtraction_round_trip x).symm
      (Eq.trans hread (regularCauchySubtraction_round_trip y)))

instance regularCauchySubtractionBHistCarrier :
    BHistCarrier RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubtractionToEventFlow
  fromEventFlow := regularCauchySubtractionFromEventFlow

instance regularCauchySubtractionChapterTasteGate :
    ChapterTasteGate RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        some x
    exact regularCauchySubtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubtractionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySubtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubtractionChapterTasteGate

theorem RegularCauchySubtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySubtractionDecodeBHist
          (regularCauchySubtractionEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchySubtractionUp,
        regularCauchySubtractionFromEventFlow
            (regularCauchySubtractionToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchySubtractionUp,
          regularCauchySubtractionToEventFlow x =
              regularCauchySubtractionToEventFlow y →
            x = y) ∧
          regularCauchySubtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchySubtraction_decode_encode,
      regularCauchySubtraction_round_trip,
      by
        intro x y heq
        exact regularCauchySubtractionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchySubtractionUp
