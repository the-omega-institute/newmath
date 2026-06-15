import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialRealCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialRealCompletionUp : Type where
  | mk (W R D Q E L H C P N : BHist) : SequentialRealCompletionUp
  deriving DecidableEq

def sequentialRealCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialRealCompletionEncodeBHist h

def sequentialRealCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialRealCompletionDecodeBHist tail)

theorem SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialRealCompletionFields :
    SequentialRealCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialRealCompletionUp.mk W R D Q E L H C P N =>
      [W, R, D, Q, E, L, H, C, P, N]

def sequentialRealCompletionToEventFlow :
    SequentialRealCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (sequentialRealCompletionFields x).map
        sequentialRealCompletionEncodeBHist

def sequentialRealCompletionEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      sequentialRealCompletionEventAtDefault index rest

def sequentialRealCompletionFromEventFlow
    (ef : EventFlow) : Option SequentialRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialRealCompletionUp.mk
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 0 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 1 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 2 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 3 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 4 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 5 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 6 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 7 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 8 ef))
      (sequentialRealCompletionDecodeBHist
        (sequentialRealCompletionEventAtDefault 9 ef)))

theorem SequentialRealCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : SequentialRealCompletionUp,
      sequentialRealCompletionFromEventFlow
        (sequentialRealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D Q E L H C P N =>
      change
        some
          (SequentialRealCompletionUp.mk
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist W))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist R))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist D))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist Q))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist E))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist L))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist H))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist C))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist P))
            (sequentialRealCompletionDecodeBHist
              (sequentialRealCompletionEncodeBHist N))) =
          some (SequentialRealCompletionUp.mk W R D Q E L H C P N)
      rw [SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode W,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode R,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode D,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode E,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode L,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode H,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode C,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode P,
        SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode N]

theorem SequentialRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialRealCompletionUp} :
    sequentialRealCompletionToEventFlow x =
      sequentialRealCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialRealCompletionFromEventFlow
          (sequentialRealCompletionToEventFlow x) =
        sequentialRealCompletionFromEventFlow
          (sequentialRealCompletionToEventFlow y) :=
    congrArg sequentialRealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SequentialRealCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentialRealCompletionTasteGate_single_carrier_alignment_round_trip y)))

theorem SequentialRealCompletionTasteGate_single_carrier_alignment_field_faithful :
    forall x y : SequentialRealCompletionUp,
      sequentialRealCompletionFields x =
        sequentialRealCompletionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ R₁ D₁ Q₁ E₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ R₂ D₂ Q₂ E₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance sequentialRealCompletionBHistCarrier :
    BHistCarrier SequentialRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialRealCompletionToEventFlow
  fromEventFlow := sequentialRealCompletionFromEventFlow

instance sequentialRealCompletionChapterTasteGate :
    ChapterTasteGate SequentialRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id
      (SequentialRealCompletionTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentialRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance sequentialRealCompletionFieldFaithful :
    FieldFaithful SequentialRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentialRealCompletionFields
  field_faithful :=
    SequentialRealCompletionTasteGate_single_carrier_alignment_field_faithful

def sequentialRealCompletionTasteGate :
    ChapterTasteGate SequentialRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentialRealCompletionChapterTasteGate

theorem SequentialRealCompletionTasteGate_single_carrier_alignment :
    (sequentialRealCompletionEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist,
        sequentialRealCompletionDecodeBHist
          (sequentialRealCompletionEncodeBHist h) = h) ∧
      (∀ x : SequentialRealCompletionUp,
        sequentialRealCompletionFromEventFlow
          (sequentialRealCompletionToEventFlow x) = some x) ∧
      (∀ x y : SequentialRealCompletionUp,
        sequentialRealCompletionFields x =
          sequentialRealCompletionFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      SequentialRealCompletionTasteGate_single_carrier_alignment_decode_encode,
      SequentialRealCompletionTasteGate_single_carrier_alignment_round_trip,
      SequentialRealCompletionTasteGate_single_carrier_alignment_field_faithful⟩

end BEDC.Derived.SequentialRealCompletionUp.TasteGate
