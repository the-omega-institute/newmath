import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialUniformCompletionUp : Type where
  | mk (S M F D H C P N : BHist) : SequentialUniformCompletionUp
  deriving DecidableEq

def sequentialUniformCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialUniformCompletionEncodeBHist h

def sequentialUniformCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialUniformCompletionDecodeBHist tail)

private theorem SequentialUniformCompletionTasteGate_decode_encode :
    forall h : BHist,
      sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialUniformCompletionFields : SequentialUniformCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialUniformCompletionUp.mk S M F D H C P N => [S, M, F, D, H, C, P, N]

def sequentialUniformCompletionToEventFlow : SequentialUniformCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialUniformCompletionFields x).map sequentialUniformCompletionEncodeBHist

private def sequentialUniformCompletionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialUniformCompletionEventAtDefault index rest

def sequentialUniformCompletionFromEventFlow (ef : EventFlow) : Option SequentialUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialUniformCompletionUp.mk
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 0 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 1 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 2 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 3 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 4 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 5 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 6 ef))
      (sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEventAtDefault 7 ef)))

private theorem SequentialUniformCompletionTasteGate_round_trip :
    forall x : SequentialUniformCompletionUp,
      sequentialUniformCompletionFromEventFlow
        (sequentialUniformCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M F D H C P N =>
      change
        some
          (SequentialUniformCompletionUp.mk
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist S))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist M))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist F))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist D))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist H))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist C))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist P))
            (sequentialUniformCompletionDecodeBHist
              (sequentialUniformCompletionEncodeBHist N))) =
          some (SequentialUniformCompletionUp.mk S M F D H C P N)
      rw [SequentialUniformCompletionTasteGate_decode_encode S,
        SequentialUniformCompletionTasteGate_decode_encode M,
        SequentialUniformCompletionTasteGate_decode_encode F,
        SequentialUniformCompletionTasteGate_decode_encode D,
        SequentialUniformCompletionTasteGate_decode_encode H,
        SequentialUniformCompletionTasteGate_decode_encode C,
        SequentialUniformCompletionTasteGate_decode_encode P,
        SequentialUniformCompletionTasteGate_decode_encode N]

private theorem SequentialUniformCompletionTasteGate_toEventFlow_injective
    {x y : SequentialUniformCompletionUp} :
    sequentialUniformCompletionToEventFlow x = sequentialUniformCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialUniformCompletionFromEventFlow (sequentialUniformCompletionToEventFlow x) =
        sequentialUniformCompletionFromEventFlow (sequentialUniformCompletionToEventFlow y) :=
    congrArg sequentialUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentialUniformCompletionTasteGate_round_trip x).symm
      (Eq.trans hread (SequentialUniformCompletionTasteGate_round_trip y)))

private theorem SequentialUniformCompletionTasteGate_field_faithful :
    forall x y : SequentialUniformCompletionUp,
      sequentialUniformCompletionFields x = sequentialUniformCompletionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ F₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ F₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance sequentialUniformCompletionBHistCarrier :
    BHistCarrier SequentialUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialUniformCompletionToEventFlow
  fromEventFlow := sequentialUniformCompletionFromEventFlow

instance sequentialUniformCompletionChapterTasteGate :
    ChapterTasteGate SequentialUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentialUniformCompletionFromEventFlow (sequentialUniformCompletionToEventFlow x) =
        some x
    exact SequentialUniformCompletionTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequentialUniformCompletionTasteGate_toEventFlow_injective heq)

instance sequentialUniformCompletionFieldFaithful :
    FieldFaithful SequentialUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentialUniformCompletionFields
  field_faithful := SequentialUniformCompletionTasteGate_field_faithful

instance sequentialUniformCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SequentialUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SequentialUniformCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SequentialUniformCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SequentialUniformCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      sequentialUniformCompletionDecodeBHist
        (sequentialUniformCompletionEncodeBHist h) = h) ∧
      (forall x : SequentialUniformCompletionUp,
        sequentialUniformCompletionFromEventFlow
          (sequentialUniformCompletionToEventFlow x) = some x) ∧
        (forall x y : SequentialUniformCompletionUp,
          sequentialUniformCompletionToEventFlow x =
            sequentialUniformCompletionToEventFlow y -> x = y) ∧
          sequentialUniformCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨SequentialUniformCompletionTasteGate_decode_encode,
      SequentialUniformCompletionTasteGate_round_trip,
      (fun _ _ heq => SequentialUniformCompletionTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SequentialUniformCompletionUp
