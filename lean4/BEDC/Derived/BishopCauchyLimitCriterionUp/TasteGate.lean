import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyLimitCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyLimitCriterionUp : Type where
  | mk (S R D M F E H C P N : BHist) : BishopCauchyLimitCriterionUp
  deriving DecidableEq

def bishopCauchyLimitCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyLimitCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyLimitCriterionEncodeBHist h

def bishopCauchyLimitCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyLimitCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyLimitCriterionDecodeBHist tail)

private theorem bishopCauchyLimitCriterion_decode_encode_bhist :
    ∀ h : BHist,
      bishopCauchyLimitCriterionDecodeBHist
        (bishopCauchyLimitCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyLimitCriterionFields : BishopCauchyLimitCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyLimitCriterionUp.mk S R D M F E H C P N => [S, R, D, M, F, E, H, C, P, N]

def bishopCauchyLimitCriterionToEventFlow : BishopCauchyLimitCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyLimitCriterionFields x).map bishopCauchyLimitCriterionEncodeBHist

private def bishopCauchyLimitCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyLimitCriterionEventAtDefault index rest

def bishopCauchyLimitCriterionFromEventFlow
    (ef : EventFlow) : Option BishopCauchyLimitCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyLimitCriterionUp.mk
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 0 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 1 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 2 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 3 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 4 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 5 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 6 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 7 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 8 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAtDefault 9 ef)))

private theorem bishopCauchyLimitCriterion_round_trip :
    ∀ x : BishopCauchyLimitCriterionUp,
      bishopCauchyLimitCriterionFromEventFlow
        (bishopCauchyLimitCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D M F E H C P N =>
      change
        some
          (BishopCauchyLimitCriterionUp.mk
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist S))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist R))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist D))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist M))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist F))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist E))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist H))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist C))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist P))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist N))) =
          some (BishopCauchyLimitCriterionUp.mk S R D M F E H C P N)
      rw [bishopCauchyLimitCriterion_decode_encode_bhist S,
        bishopCauchyLimitCriterion_decode_encode_bhist R,
        bishopCauchyLimitCriterion_decode_encode_bhist D,
        bishopCauchyLimitCriterion_decode_encode_bhist M,
        bishopCauchyLimitCriterion_decode_encode_bhist F,
        bishopCauchyLimitCriterion_decode_encode_bhist E,
        bishopCauchyLimitCriterion_decode_encode_bhist H,
        bishopCauchyLimitCriterion_decode_encode_bhist C,
        bishopCauchyLimitCriterion_decode_encode_bhist P,
        bishopCauchyLimitCriterion_decode_encode_bhist N]

private theorem bishopCauchyLimitCriterionToEventFlow_injective
    {x y : BishopCauchyLimitCriterionUp} :
    bishopCauchyLimitCriterionToEventFlow x = bishopCauchyLimitCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyLimitCriterionFromEventFlow
          (bishopCauchyLimitCriterionToEventFlow x) =
        bishopCauchyLimitCriterionFromEventFlow
          (bishopCauchyLimitCriterionToEventFlow y) :=
    congrArg bishopCauchyLimitCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCauchyLimitCriterion_round_trip x).symm
      (Eq.trans hread (bishopCauchyLimitCriterion_round_trip y)))

instance bishopCauchyLimitCriterionBHistCarrier :
    BHistCarrier BishopCauchyLimitCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyLimitCriterionToEventFlow
  fromEventFlow := bishopCauchyLimitCriterionFromEventFlow

instance bishopCauchyLimitCriterionChapterTasteGate :
    ChapterTasteGate BishopCauchyLimitCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyLimitCriterionFromEventFlow
        (bishopCauchyLimitCriterionToEventFlow x) = some x
    exact bishopCauchyLimitCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyLimitCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyLimitCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyLimitCriterionChapterTasteGate

theorem BishopCauchyLimitCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCauchyLimitCriterionDecodeBHist
        (bishopCauchyLimitCriterionEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyLimitCriterionUp,
        bishopCauchyLimitCriterionFromEventFlow
          (bishopCauchyLimitCriterionToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyLimitCriterionUp,
          bishopCauchyLimitCriterionToEventFlow x =
            bishopCauchyLimitCriterionToEventFlow y → x = y) ∧
          bishopCauchyLimitCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopCauchyLimitCriterion_decode_encode_bhist,
      bishopCauchyLimitCriterion_round_trip,
      (fun _ _ heq => bishopCauchyLimitCriterionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopCauchyLimitCriterionUp
