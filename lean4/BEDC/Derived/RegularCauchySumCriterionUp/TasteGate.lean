import BEDC.Derived.RegularCauchySumCriterionUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySumCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchySumCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySumCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySumCriterionEncodeBHist h

def regularCauchySumCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySumCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySumCriterionDecodeBHist tail)

private theorem regularCauchySumCriterion_decode_encode :
    ∀ h : BHist,
      regularCauchySumCriterionDecodeBHist
          (regularCauchySumCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def regularCauchySumCriterionFields :
    RegularCauchySumCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySumCriterionUp.mk A B WA WB D L R E H C P N =>
      [A, B, WA, WB, D, L, R, E, H, C, P, N]

def regularCauchySumCriterionToEventFlow :
    RegularCauchySumCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchySumCriterionFields x).map
        regularCauchySumCriterionEncodeBHist

private def regularCauchySumCriterionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchySumCriterionEventAtDefault index rest

def regularCauchySumCriterionFromEventFlow
    (ef : EventFlow) : Option RegularCauchySumCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySumCriterionUp.mk
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 0 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 1 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 2 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 3 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 4 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 5 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 6 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 7 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 8 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 9 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 10 ef))
      (regularCauchySumCriterionDecodeBHist
        (regularCauchySumCriterionEventAtDefault 11 ef)))

private theorem regularCauchySumCriterion_round_trip :
    ∀ x : RegularCauchySumCriterionUp,
      regularCauchySumCriterionFromEventFlow
          (regularCauchySumCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB D L R E H C P N =>
      change
        some
          (RegularCauchySumCriterionUp.mk
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist A))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist B))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist WA))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist WB))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist D))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist L))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist R))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist E))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist H))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist C))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist P))
            (regularCauchySumCriterionDecodeBHist
              (regularCauchySumCriterionEncodeBHist N))) =
          some (RegularCauchySumCriterionUp.mk A B WA WB D L R E H C P N)
      rw [regularCauchySumCriterion_decode_encode A,
        regularCauchySumCriterion_decode_encode B,
        regularCauchySumCriterion_decode_encode WA,
        regularCauchySumCriterion_decode_encode WB,
        regularCauchySumCriterion_decode_encode D,
        regularCauchySumCriterion_decode_encode L,
        regularCauchySumCriterion_decode_encode R,
        regularCauchySumCriterion_decode_encode E,
        regularCauchySumCriterion_decode_encode H,
        regularCauchySumCriterion_decode_encode C,
        regularCauchySumCriterion_decode_encode P,
        regularCauchySumCriterion_decode_encode N]

private theorem regularCauchySumCriterionToEventFlow_injective
    {x y : RegularCauchySumCriterionUp} :
    regularCauchySumCriterionToEventFlow x =
        regularCauchySumCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySumCriterionFromEventFlow
          (regularCauchySumCriterionToEventFlow x) =
        regularCauchySumCriterionFromEventFlow
          (regularCauchySumCriterionToEventFlow y) :=
    congrArg regularCauchySumCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySumCriterion_round_trip x).symm
      (Eq.trans hread (regularCauchySumCriterion_round_trip y)))

instance regularCauchySumCriterionBHistCarrier :
    BHistCarrier RegularCauchySumCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySumCriterionToEventFlow
  fromEventFlow := regularCauchySumCriterionFromEventFlow

instance regularCauchySumCriterionChapterTasteGate :
    ChapterTasteGate RegularCauchySumCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySumCriterionFromEventFlow
          (regularCauchySumCriterionToEventFlow x) =
        some x
    exact regularCauchySumCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySumCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySumCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySumCriterionChapterTasteGate

theorem RegularCauchySumCriterionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchySumCriterionUp) ∧
      Nonempty (ChapterTasteGate RegularCauchySumCriterionUp) ∧
      (∀ h : BHist,
        regularCauchySumCriterionDecodeBHist
            (regularCauchySumCriterionEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchySumCriterionUp,
        regularCauchySumCriterionFromEventFlow
            (regularCauchySumCriterionToEventFlow x) =
          some x) ∧
      regularCauchySumCriterionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact Nonempty.intro regularCauchySumCriterionBHistCarrier
  constructor
  · exact Nonempty.intro regularCauchySumCriterionChapterTasteGate
  constructor
  · exact regularCauchySumCriterion_decode_encode
  constructor
  · exact regularCauchySumCriterion_round_trip
  · rfl

end BEDC.Derived.RegularCauchySumCriterionUp
