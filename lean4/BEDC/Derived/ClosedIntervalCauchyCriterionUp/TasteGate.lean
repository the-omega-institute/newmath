import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalCauchyCriterionUp : Type where
  | mk (A B I F W T S R E H C P N : BHist) : ClosedIntervalCauchyCriterionUp
  deriving DecidableEq

def closedIntervalCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalCauchyCriterionEncodeBHist h

def closedIntervalCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalCauchyCriterionDecodeBHist tail)

private theorem closedIntervalCauchyCriterionDecode_encode_bhist :
    ∀ h : BHist,
      closedIntervalCauchyCriterionDecodeBHist
        (closedIntervalCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalCauchyCriterionToEventFlow :
    ClosedIntervalCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalCauchyCriterionUp.mk A B I F W T S R E H C P N =>
      [closedIntervalCauchyCriterionEncodeBHist A,
        closedIntervalCauchyCriterionEncodeBHist B,
        closedIntervalCauchyCriterionEncodeBHist I,
        closedIntervalCauchyCriterionEncodeBHist F,
        closedIntervalCauchyCriterionEncodeBHist W,
        closedIntervalCauchyCriterionEncodeBHist T,
        closedIntervalCauchyCriterionEncodeBHist S,
        closedIntervalCauchyCriterionEncodeBHist R,
        closedIntervalCauchyCriterionEncodeBHist E,
        closedIntervalCauchyCriterionEncodeBHist H,
        closedIntervalCauchyCriterionEncodeBHist C,
        closedIntervalCauchyCriterionEncodeBHist P,
        closedIntervalCauchyCriterionEncodeBHist N]

private def closedIntervalCauchyCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedIntervalCauchyCriterionEventAt index rest

def closedIntervalCauchyCriterionFromEventFlow :
    EventFlow → Option ClosedIntervalCauchyCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ClosedIntervalCauchyCriterionUp.mk
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 0 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 1 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 2 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 3 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 4 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 5 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 6 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 7 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 8 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 9 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 10 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 11 ef))
          (closedIntervalCauchyCriterionDecodeBHist
            (closedIntervalCauchyCriterionEventAt 12 ef)))

private theorem closedIntervalCauchyCriterion_round_trip :
    ∀ x : ClosedIntervalCauchyCriterionUp,
      closedIntervalCauchyCriterionFromEventFlow
        (closedIntervalCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B I F W T S R E H C P N =>
      change
        some
          (ClosedIntervalCauchyCriterionUp.mk
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist A))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist B))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist I))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist F))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist W))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist T))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist S))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist R))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist E))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist H))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist C))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist P))
            (closedIntervalCauchyCriterionDecodeBHist
              (closedIntervalCauchyCriterionEncodeBHist N))) =
          some (ClosedIntervalCauchyCriterionUp.mk A B I F W T S R E H C P N)
      rw [closedIntervalCauchyCriterionDecode_encode_bhist A,
        closedIntervalCauchyCriterionDecode_encode_bhist B,
        closedIntervalCauchyCriterionDecode_encode_bhist I,
        closedIntervalCauchyCriterionDecode_encode_bhist F,
        closedIntervalCauchyCriterionDecode_encode_bhist W,
        closedIntervalCauchyCriterionDecode_encode_bhist T,
        closedIntervalCauchyCriterionDecode_encode_bhist S,
        closedIntervalCauchyCriterionDecode_encode_bhist R,
        closedIntervalCauchyCriterionDecode_encode_bhist E,
        closedIntervalCauchyCriterionDecode_encode_bhist H,
        closedIntervalCauchyCriterionDecode_encode_bhist C,
        closedIntervalCauchyCriterionDecode_encode_bhist P,
        closedIntervalCauchyCriterionDecode_encode_bhist N]

private theorem closedIntervalCauchyCriterionToEventFlow_injective
    {x y : ClosedIntervalCauchyCriterionUp} :
    closedIntervalCauchyCriterionToEventFlow x =
      closedIntervalCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalCauchyCriterionFromEventFlow
          (closedIntervalCauchyCriterionToEventFlow x) =
        closedIntervalCauchyCriterionFromEventFlow
          (closedIntervalCauchyCriterionToEventFlow y) :=
    congrArg closedIntervalCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedIntervalCauchyCriterion_round_trip x).symm
      (Eq.trans hread (closedIntervalCauchyCriterion_round_trip y)))

instance closedIntervalCauchyCriterionBHistCarrier :
    BHistCarrier ClosedIntervalCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalCauchyCriterionToEventFlow
  fromEventFlow := closedIntervalCauchyCriterionFromEventFlow

instance closedIntervalCauchyCriterionChapterTasteGate :
    ChapterTasteGate ClosedIntervalCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalCauchyCriterionFromEventFlow
        (closedIntervalCauchyCriterionToEventFlow x) = some x
    exact closedIntervalCauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedIntervalCauchyCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedIntervalCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalCauchyCriterionChapterTasteGate

namespace TasteGate

theorem ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedIntervalCauchyCriterionUp) ∧
      (∀ h : BHist,
        closedIntervalCauchyCriterionDecodeBHist
          (closedIntervalCauchyCriterionEncodeBHist h) = h) ∧
      (∀ x : ClosedIntervalCauchyCriterionUp,
        closedIntervalCauchyCriterionFromEventFlow
          (closedIntervalCauchyCriterionToEventFlow x) = some x) ∧
      (∀ x y : ClosedIntervalCauchyCriterionUp,
        closedIntervalCauchyCriterionToEventFlow x =
          closedIntervalCauchyCriterionToEventFlow y → x = y) ∧
      closedIntervalCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨closedIntervalCauchyCriterionChapterTasteGate⟩,
      closedIntervalCauchyCriterionDecode_encode_bhist,
      closedIntervalCauchyCriterion_round_trip,
      (fun _ _ heq => closedIntervalCauchyCriterionToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.ClosedIntervalCauchyCriterionUp
