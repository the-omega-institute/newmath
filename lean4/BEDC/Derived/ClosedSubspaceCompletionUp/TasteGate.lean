import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSubspaceCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSubspaceCompletionUp : Type where
  | mk (parent subspace closedness inheritedLimit transport replay provenance name : BHist) :
      ClosedSubspaceCompletionUp
  deriving DecidableEq

def closedSubspaceCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSubspaceCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSubspaceCompletionEncodeBHist h

def closedSubspaceCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSubspaceCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSubspaceCompletionDecodeBHist tail)

private theorem closedSubspaceCompletionDecode_encode :
    ∀ h : BHist, closedSubspaceCompletionDecodeBHist
        (closedSubspaceCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedSubspaceCompletionFields : ClosedSubspaceCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSubspaceCompletionUp.mk parent subspace closedness inheritedLimit transport replay
      provenance name =>
      [parent, subspace, closedness, inheritedLimit, transport, replay, provenance, name]

def closedSubspaceCompletionToEventFlow : ClosedSubspaceCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSubspaceCompletionUp.mk parent subspace closedness inheritedLimit transport replay
      provenance name =>
      [closedSubspaceCompletionEncodeBHist parent, closedSubspaceCompletionEncodeBHist subspace,
        closedSubspaceCompletionEncodeBHist closedness,
        closedSubspaceCompletionEncodeBHist inheritedLimit,
        closedSubspaceCompletionEncodeBHist transport, closedSubspaceCompletionEncodeBHist replay,
        closedSubspaceCompletionEncodeBHist provenance, closedSubspaceCompletionEncodeBHist name]

private def closedSubspaceCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedSubspaceCompletionEventAt index rest

def closedSubspaceCompletionFromEventFlow : EventFlow → Option ClosedSubspaceCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ClosedSubspaceCompletionUp.mk
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 0 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 1 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 2 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 3 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 4 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 5 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 6 ef))
        (closedSubspaceCompletionDecodeBHist (closedSubspaceCompletionEventAt 7 ef)))

private theorem closedSubspaceCompletionRoundTrip :
    ∀ x : ClosedSubspaceCompletionUp,
      closedSubspaceCompletionFromEventFlow (closedSubspaceCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk parent subspace closedness inheritedLimit transport replay provenance name =>
      change
        some
            (ClosedSubspaceCompletionUp.mk
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist parent))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist subspace))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist closedness))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist inheritedLimit))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist transport))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist replay))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist provenance))
              (closedSubspaceCompletionDecodeBHist
                (closedSubspaceCompletionEncodeBHist name))) =
          some
            (ClosedSubspaceCompletionUp.mk parent subspace closedness inheritedLimit transport
              replay provenance name)
      rw [closedSubspaceCompletionDecode_encode parent,
        closedSubspaceCompletionDecode_encode subspace,
        closedSubspaceCompletionDecode_encode closedness,
        closedSubspaceCompletionDecode_encode inheritedLimit,
        closedSubspaceCompletionDecode_encode transport,
        closedSubspaceCompletionDecode_encode replay,
        closedSubspaceCompletionDecode_encode provenance,
        closedSubspaceCompletionDecode_encode name]

private theorem closedSubspaceCompletionToEventFlow_injective
    {x y : ClosedSubspaceCompletionUp} :
    closedSubspaceCompletionToEventFlow x = closedSubspaceCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          closedSubspaceCompletionFromEventFlow (closedSubspaceCompletionToEventFlow x) :=
        (closedSubspaceCompletionRoundTrip x).symm
      _ = closedSubspaceCompletionFromEventFlow (closedSubspaceCompletionToEventFlow y) :=
        congrArg closedSubspaceCompletionFromEventFlow hxy
      _ = some y := closedSubspaceCompletionRoundTrip y
  exact Option.some.inj optionEq

private theorem closedSubspaceCompletionFieldFaithfulProof :
    ∀ x y : ClosedSubspaceCompletionUp,
      closedSubspaceCompletionFields x = closedSubspaceCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk parent₁ subspace₁ closedness₁ inheritedLimit₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk parent₂ subspace₂ closedness₂ inheritedLimit₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance closedSubspaceCompletionBHistCarrier : BHistCarrier ClosedSubspaceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSubspaceCompletionToEventFlow
  fromEventFlow := closedSubspaceCompletionFromEventFlow

instance closedSubspaceCompletionChapterTasteGate : ChapterTasteGate ClosedSubspaceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedSubspaceCompletionFromEventFlow (closedSubspaceCompletionToEventFlow x) = some x
    exact closedSubspaceCompletionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedSubspaceCompletionToEventFlow_injective heq)

instance closedSubspaceCompletionFieldFaithful : FieldFaithful ClosedSubspaceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedSubspaceCompletionFields
  field_faithful := closedSubspaceCompletionFieldFaithfulProof

instance closedSubspaceCompletionNontrivial : Nontrivial ClosedSubspaceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedSubspaceCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedSubspaceCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def closedSubspaceCompletionTasteGate : ChapterTasteGate ClosedSubspaceCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedSubspaceCompletionChapterTasteGate

theorem ClosedSubspaceCompletionTasteGate_single_carrier_alignment :
      (forall h : BHist, closedSubspaceCompletionDecodeBHist
        (closedSubspaceCompletionEncodeBHist h) = h) ∧
      (forall x : ClosedSubspaceCompletionUp,
        closedSubspaceCompletionFromEventFlow (closedSubspaceCompletionToEventFlow x) =
          some x) ∧
      (forall x y : ClosedSubspaceCompletionUp,
        closedSubspaceCompletionToEventFlow x = closedSubspaceCompletionToEventFlow y →
          x = y) ∧
      closedSubspaceCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedSubspaceCompletionDecode_encode
  constructor
  · exact closedSubspaceCompletionRoundTrip
  constructor
  · intro x y
    exact closedSubspaceCompletionToEventFlow_injective
  · rfl

end BEDC.Derived.ClosedSubspaceCompletionUp
