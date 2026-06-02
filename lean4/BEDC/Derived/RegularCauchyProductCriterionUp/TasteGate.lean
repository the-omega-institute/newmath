import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyProductCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyProductCriterionUp : Type where
  | mk (A B WA WB D P K R E H C L N : BHist) : RegularCauchyProductCriterionUp
  deriving DecidableEq

def regularCauchyProductCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyProductCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyProductCriterionEncodeBHist h

def regularCauchyProductCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyProductCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyProductCriterionDecodeBHist tail)

private theorem regularCauchyProductCriterion_decode_encode :
    ∀ h : BHist,
      regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def regularCauchyProductCriterionFields :
    RegularCauchyProductCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyProductCriterionUp.mk A B WA WB D P K R E H C L N =>
      [A, B, WA, WB, D, P, K, R, E, H, C, L, N]

def regularCauchyProductCriterionToEventFlow :
    RegularCauchyProductCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyProductCriterionFields x).map
        regularCauchyProductCriterionEncodeBHist

private def regularCauchyProductCriterionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyProductCriterionEventAtDefault index rest

def regularCauchyProductCriterionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyProductCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyProductCriterionUp.mk
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 0 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 1 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 2 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 3 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 4 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 5 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 6 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 7 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 8 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 9 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 10 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 11 ef))
      (regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEventAtDefault 12 ef)))

private theorem regularCauchyProductCriterion_round_trip :
    ∀ x : RegularCauchyProductCriterionUp,
      regularCauchyProductCriterionFromEventFlow
        (regularCauchyProductCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB D P K R E H C L N =>
      change
        some
          (RegularCauchyProductCriterionUp.mk
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist A))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist B))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist WA))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist WB))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist D))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist P))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist K))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist R))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist E))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist H))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist C))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist L))
            (regularCauchyProductCriterionDecodeBHist
              (regularCauchyProductCriterionEncodeBHist N))) =
          some (RegularCauchyProductCriterionUp.mk A B WA WB D P K R E H C L N)
      rw [regularCauchyProductCriterion_decode_encode A,
        regularCauchyProductCriterion_decode_encode B,
        regularCauchyProductCriterion_decode_encode WA,
        regularCauchyProductCriterion_decode_encode WB,
        regularCauchyProductCriterion_decode_encode D,
        regularCauchyProductCriterion_decode_encode P,
        regularCauchyProductCriterion_decode_encode K,
        regularCauchyProductCriterion_decode_encode R,
        regularCauchyProductCriterion_decode_encode E,
        regularCauchyProductCriterion_decode_encode H,
        regularCauchyProductCriterion_decode_encode C,
        regularCauchyProductCriterion_decode_encode L,
        regularCauchyProductCriterion_decode_encode N]

private theorem regularCauchyProductCriterionToEventFlow_injective
    {x y : RegularCauchyProductCriterionUp} :
    regularCauchyProductCriterionToEventFlow x =
      regularCauchyProductCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyProductCriterionFromEventFlow
          (regularCauchyProductCriterionToEventFlow x) =
        regularCauchyProductCriterionFromEventFlow
          (regularCauchyProductCriterionToEventFlow y) :=
    congrArg regularCauchyProductCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyProductCriterion_round_trip x).symm
      (Eq.trans hread (regularCauchyProductCriterion_round_trip y)))

instance regularCauchyProductCriterionBHistCarrier :
    BHistCarrier RegularCauchyProductCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyProductCriterionToEventFlow
  fromEventFlow := regularCauchyProductCriterionFromEventFlow

instance regularCauchyProductCriterionChapterTasteGate :
    ChapterTasteGate RegularCauchyProductCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyProductCriterionFromEventFlow
        (regularCauchyProductCriterionToEventFlow x) = some x
    exact regularCauchyProductCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyProductCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyProductCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyProductCriterionChapterTasteGate

theorem RegularCauchyProductCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyProductCriterionDecodeBHist
        (regularCauchyProductCriterionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyProductCriterionUp,
        regularCauchyProductCriterionFromEventFlow
          (regularCauchyProductCriterionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyProductCriterionUp,
          regularCauchyProductCriterionToEventFlow x =
            regularCauchyProductCriterionToEventFlow y → x = y) ∧
          regularCauchyProductCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact regularCauchyProductCriterion_decode_encode
  constructor
  · exact regularCauchyProductCriterion_round_trip
  constructor
  · intro x y heq
    exact regularCauchyProductCriterionToEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularCauchyProductCriterionUp
