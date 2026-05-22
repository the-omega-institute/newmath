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

private theorem ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedIntervalCauchyCriterionDecodeBHist
          (closedIntervalCauchyCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalCauchyCriterionFields :
    ClosedIntervalCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalCauchyCriterionUp.mk A B I F W T S R E H C P N =>
      [A, B, I, F, W, T, S, R, E, H, C, P, N]

def closedIntervalCauchyCriterionToEventFlow :
    ClosedIntervalCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedIntervalCauchyCriterionFields x).map closedIntervalCauchyCriterionEncodeBHist

private def closedIntervalCauchyCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedIntervalCauchyCriterionEventAt index rest

def closedIntervalCauchyCriterionFromEventFlow
    (ef : EventFlow) : Option ClosedIntervalCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalCauchyCriterionUp.mk
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 0 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 1 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 2 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 3 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 4 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 5 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 6 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 7 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 8 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 9 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 10 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 11 ef))
      (closedIntervalCauchyCriterionDecodeBHist (closedIntervalCauchyCriterionEventAt 12 ef)))

private theorem ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_round_trip
    (x : ClosedIntervalCauchyCriterionUp) :
    closedIntervalCauchyCriterionFromEventFlow
        (closedIntervalCauchyCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
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
      rw [ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode A,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode B,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode I,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode F,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode W,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode T,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode S,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode E,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedIntervalCauchyCriterionUp} :
    closedIntervalCauchyCriterionToEventFlow x =
        closedIntervalCauchyCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalCauchyCriterionFromEventFlow
          (closedIntervalCauchyCriterionToEventFlow x) =
        closedIntervalCauchyCriterionFromEventFlow
          (closedIntervalCauchyCriterionToEventFlow y) :=
    congrArg closedIntervalCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ClosedIntervalCauchyCriterionUp,
      closedIntervalCauchyCriterionFields x = closedIntervalCauchyCriterionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ I₁ F₁ W₁ T₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ I₂ F₂ W₂ T₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

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
          (closedIntervalCauchyCriterionToEventFlow x) =
        some x
    exact ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance closedIntervalCauchyCriterionFieldFaithful :
    FieldFaithful ClosedIntervalCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedIntervalCauchyCriterionFields
  field_faithful :=
    ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_fields_faithful

instance closedIntervalCauchyCriterionNontrivial :
    Nontrivial ClosedIntervalCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedIntervalCauchyCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedIntervalCauchyCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ClosedIntervalCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalCauchyCriterionChapterTasteGate

theorem ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedIntervalCauchyCriterionDecodeBHist
          (closedIntervalCauchyCriterionEncodeBHist h) =
        h) ∧
      (∀ x : ClosedIntervalCauchyCriterionUp,
        closedIntervalCauchyCriterionFromEventFlow
            (closedIntervalCauchyCriterionToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedIntervalCauchyCriterionUp,
          closedIntervalCauchyCriterionToEventFlow x =
              closedIntervalCauchyCriterionToEventFlow y →
            x = y) ∧
          closedIntervalCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_decode_encode,
      ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ClosedIntervalCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClosedIntervalCauchyCriterionUp
