import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetConvergenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetConvergenceCriterionUp : Type where
  | mk (C S R D W T E H A P N : BHist) : CauchyNetConvergenceCriterionUp
  deriving DecidableEq

def cauchyNetConvergenceCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetConvergenceCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetConvergenceCriterionEncodeBHist h

def cauchyNetConvergenceCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetConvergenceCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetConvergenceCriterionDecodeBHist tail)

private theorem cauchyNetConvergenceCriterion_decode_encode_bhist :
    ∀ h : BHist,
      cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNetConvergenceCriterionFields :
    CauchyNetConvergenceCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetConvergenceCriterionUp.mk C S R D W T E H A P N =>
      [C, S, R, D, W, T, E, H, A, P, N]

def cauchyNetConvergenceCriterionToEventFlow :
    CauchyNetConvergenceCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNetConvergenceCriterionFields x).map
      cauchyNetConvergenceCriterionEncodeBHist

private def cauchyNetConvergenceCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyNetConvergenceCriterionEventAtDefault index rest

def cauchyNetConvergenceCriterionFromEventFlow (ef : EventFlow) :
    Option CauchyNetConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyNetConvergenceCriterionUp.mk
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 0 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 1 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 2 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 3 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 4 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 5 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 6 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 7 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 8 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 9 ef))
      (cauchyNetConvergenceCriterionDecodeBHist
        (cauchyNetConvergenceCriterionEventAtDefault 10 ef)))

private theorem cauchyNetConvergenceCriterion_round_trip :
    ∀ x : CauchyNetConvergenceCriterionUp,
      cauchyNetConvergenceCriterionFromEventFlow
        (cauchyNetConvergenceCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C S R D W T E H A P N =>
      change
        some
          (CauchyNetConvergenceCriterionUp.mk
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist C))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist S))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist R))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist D))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist W))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist T))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist E))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist H))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist A))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist P))
            (cauchyNetConvergenceCriterionDecodeBHist
              (cauchyNetConvergenceCriterionEncodeBHist N))) =
          some (CauchyNetConvergenceCriterionUp.mk C S R D W T E H A P N)
      rw [cauchyNetConvergenceCriterion_decode_encode_bhist C,
        cauchyNetConvergenceCriterion_decode_encode_bhist S,
        cauchyNetConvergenceCriterion_decode_encode_bhist R,
        cauchyNetConvergenceCriterion_decode_encode_bhist D,
        cauchyNetConvergenceCriterion_decode_encode_bhist W,
        cauchyNetConvergenceCriterion_decode_encode_bhist T,
        cauchyNetConvergenceCriterion_decode_encode_bhist E,
        cauchyNetConvergenceCriterion_decode_encode_bhist H,
        cauchyNetConvergenceCriterion_decode_encode_bhist A,
        cauchyNetConvergenceCriterion_decode_encode_bhist P,
        cauchyNetConvergenceCriterion_decode_encode_bhist N]

private theorem cauchyNetConvergenceCriterionToEventFlow_injective
    {x y : CauchyNetConvergenceCriterionUp} :
    cauchyNetConvergenceCriterionToEventFlow x =
      cauchyNetConvergenceCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetConvergenceCriterionFromEventFlow
          (cauchyNetConvergenceCriterionToEventFlow x) =
        cauchyNetConvergenceCriterionFromEventFlow
          (cauchyNetConvergenceCriterionToEventFlow y) :=
    congrArg cauchyNetConvergenceCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyNetConvergenceCriterion_round_trip x).symm
      (Eq.trans hread (cauchyNetConvergenceCriterion_round_trip y)))

instance cauchyNetConvergenceCriterionBHistCarrier :
    BHistCarrier CauchyNetConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetConvergenceCriterionToEventFlow
  fromEventFlow := cauchyNetConvergenceCriterionFromEventFlow

instance cauchyNetConvergenceCriterionChapterTasteGate :
    ChapterTasteGate CauchyNetConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyNetConvergenceCriterionFromEventFlow
      (cauchyNetConvergenceCriterionToEventFlow x) = some x
    exact cauchyNetConvergenceCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyNetConvergenceCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyNetConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetConvergenceCriterionChapterTasteGate

theorem CauchyNetConvergenceCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyNetConvergenceCriterionDecodeBHist
          (cauchyNetConvergenceCriterionEncodeBHist h) = h) ∧
      cauchyNetConvergenceCriterionFields
          (CauchyNetConvergenceCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact cauchyNetConvergenceCriterion_decode_encode_bhist
  · rfl

end BEDC.Derived.CauchyNetConvergenceCriterionUp
