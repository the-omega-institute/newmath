import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitCauchyCriterionUp : Type where
  | mk (F W M S R E H C P N : BHist) : UniformLimitCauchyCriterionUp
  deriving DecidableEq

def uniformLimitCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitCauchyCriterionEncodeBHist h

def uniformLimitCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitCauchyCriterionDecodeBHist tail)

private theorem UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLimitCauchyCriterionFields :
    UniformLimitCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitCauchyCriterionUp.mk F W M S R E H C P N => [F, W, M, S, R, E, H, C, P, N]

def uniformLimitCauchyCriterionToEventFlow :
    UniformLimitCauchyCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformLimitCauchyCriterionFields x).map uniformLimitCauchyCriterionEncodeBHist

private def uniformLimitCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformLimitCauchyCriterionEventAtDefault index rest

def uniformLimitCauchyCriterionFromEventFlow
    (ef : EventFlow) : Option UniformLimitCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformLimitCauchyCriterionUp.mk
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 0 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 1 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 2 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 3 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 4 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 5 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 6 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 7 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 8 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 9 ef)))

private theorem UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_round_trip
    (x : UniformLimitCauchyCriterionUp) :
    uniformLimitCauchyCriterionFromEventFlow
      (uniformLimitCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F W M S R E H C P N =>
      change
        some
          (UniformLimitCauchyCriterionUp.mk
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist F))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist W))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist M))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist S))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist R))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist E))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist H))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist C))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist P))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist N))) =
          some (UniformLimitCauchyCriterionUp.mk F W M S R E H C P N)
      rw [UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode F,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode W,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode M,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode S,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode E,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformLimitCauchyCriterionUp} :
    uniformLimitCauchyCriterionToEventFlow x = uniformLimitCauchyCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitCauchyCriterionFromEventFlow (uniformLimitCauchyCriterionToEventFlow x) =
        uniformLimitCauchyCriterionFromEventFlow (uniformLimitCauchyCriterionToEventFlow y) :=
    congrArg uniformLimitCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance uniformLimitCauchyCriterionBHistCarrier :
    BHistCarrier UniformLimitCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitCauchyCriterionToEventFlow
  fromEventFlow := uniformLimitCauchyCriterionFromEventFlow

instance uniformLimitCauchyCriterionChapterTasteGate :
    ChapterTasteGate UniformLimitCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformLimitCauchyCriterionFromEventFlow
        (uniformLimitCauchyCriterionToEventFlow x) = some x
    exact UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformLimitCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitCauchyCriterionChapterTasteGate

theorem UniformLimitCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformLimitCauchyCriterionUp) ∧
        Nonempty (ChapterTasteGate UniformLimitCauchyCriterionUp) ∧
          uniformLimitCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformLimitCauchyCriterionTasteGate_single_carrier_alignment_decode_encode,
      ⟨uniformLimitCauchyCriterionBHistCarrier⟩,
      ⟨uniformLimitCauchyCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformLimitCauchyCriterionUp
