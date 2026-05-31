import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffUniformCompletionUp : Type where
  | mk (F D U S H C P N : BHist) : HausdorffUniformCompletionUp
  deriving DecidableEq

def hausdorffUniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffUniformCompletionEncodeBHist h

def hausdorffUniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffUniformCompletionDecodeBHist tail)

private theorem HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hausdorffUniformCompletionDecodeBHist
        (hausdorffUniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffUniformCompletionFields :
    HausdorffUniformCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffUniformCompletionUp.mk F D U S H C P N => [F, D, U, S, H, C, P, N]

def hausdorffUniformCompletionToEventFlow :
    HausdorffUniformCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hausdorffUniformCompletionFields x).map hausdorffUniformCompletionEncodeBHist

private def hausdorffUniformCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffUniformCompletionEventAtDefault index rest

def hausdorffUniformCompletionFromEventFlow (ef : EventFlow) :
    Option HausdorffUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffUniformCompletionUp.mk
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 0 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 1 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 2 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 3 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 4 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 5 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 6 ef))
      (hausdorffUniformCompletionDecodeBHist (hausdorffUniformCompletionEventAtDefault 7 ef)))

private theorem HausdorffUniformCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffUniformCompletionUp,
      hausdorffUniformCompletionFromEventFlow
        (hausdorffUniformCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F D U S H C P N =>
      change
        some
          (HausdorffUniformCompletionUp.mk
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist F))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist D))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist U))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist S))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist H))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist C))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist P))
            (hausdorffUniformCompletionDecodeBHist
              (hausdorffUniformCompletionEncodeBHist N))) =
          some (HausdorffUniformCompletionUp.mk F D U S H C P N)
      rw [HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode F,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode D,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode U,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode S,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode H,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode C,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode P,
        HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode N]

private theorem HausdorffUniformCompletionTasteGate_single_carrier_alignment_injective
    {x y : HausdorffUniformCompletionUp} :
    hausdorffUniformCompletionToEventFlow x =
      hausdorffUniformCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffUniformCompletionFromEventFlow
          (hausdorffUniformCompletionToEventFlow x) =
        hausdorffUniformCompletionFromEventFlow
          (hausdorffUniformCompletionToEventFlow y) :=
    congrArg hausdorffUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HausdorffUniformCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffUniformCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem hausdorffUniformCompletionFields_faithful :
    ∀ x y : HausdorffUniformCompletionUp,
      hausdorffUniformCompletionFields x = hausdorffUniformCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ D₁ U₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ D₂ U₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hausdorffUniformCompletionBHistCarrier :
    BHistCarrier HausdorffUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffUniformCompletionToEventFlow
  fromEventFlow := hausdorffUniformCompletionFromEventFlow

instance hausdorffUniformCompletionChapterTasteGate :
    ChapterTasteGate HausdorffUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffUniformCompletionFromEventFlow
        (hausdorffUniformCompletionToEventFlow x) = some x
    exact HausdorffUniformCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffUniformCompletionTasteGate_single_carrier_alignment_injective heq)

instance hausdorffUniformCompletionFieldFaithful :
    FieldFaithful HausdorffUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffUniformCompletionFields
  field_faithful := hausdorffUniformCompletionFields_faithful

instance hausdorffUniformCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HausdorffUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffUniformCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffUniformCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def hausdorffUniformCompletionTasteGate :
    ChapterTasteGate HausdorffUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffUniformCompletionChapterTasteGate

theorem HausdorffUniformCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hausdorffUniformCompletionDecodeBHist
        (hausdorffUniformCompletionEncodeBHist h) = h) ∧
      (∀ x : HausdorffUniformCompletionUp,
        hausdorffUniformCompletionFromEventFlow
          (hausdorffUniformCompletionToEventFlow x) = some x) ∧
      (∀ x y : HausdorffUniformCompletionUp,
        hausdorffUniformCompletionToEventFlow x =
          hausdorffUniformCompletionToEventFlow y → x = y) ∧
      hausdorffUniformCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact HausdorffUniformCompletionTasteGate_single_carrier_alignment_decode
  constructor
  · exact HausdorffUniformCompletionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact HausdorffUniformCompletionTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.HausdorffUniformCompletionUp
