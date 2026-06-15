import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionUp : Type where
  | mk (M S E W R D A H C P N : BHist) : LocatedCompletionUp
  deriving DecidableEq

def locatedCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionEncodeBHist h

def locatedCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionDecodeBHist tail)

private theorem locatedCompletion_decode_encode :
    ∀ h : BHist,
      locatedCompletionDecodeBHist (locatedCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionFields : LocatedCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionUp.mk M S E W R D A H C P N => [M, S, E, W, R, D, A, H, C, P, N]

def locatedCompletionToEventFlow : LocatedCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCompletionFields x).map locatedCompletionEncodeBHist

private def locatedCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompletionEventAtDefault index rest

def locatedCompletionFromEventFlow (ef : EventFlow) : Option LocatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompletionUp.mk
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 0 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 1 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 2 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 3 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 4 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 5 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 6 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 7 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 8 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 9 ef))
      (locatedCompletionDecodeBHist (locatedCompletionEventAtDefault 10 ef)))

private theorem locatedCompletion_round_trip :
    ∀ x : LocatedCompletionUp,
      locatedCompletionFromEventFlow (locatedCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S E W R D A H C P N =>
      change
        some
          (LocatedCompletionUp.mk
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist M))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist S))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist E))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist W))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist R))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist D))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist A))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist H))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist C))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist P))
            (locatedCompletionDecodeBHist (locatedCompletionEncodeBHist N))) =
          some (LocatedCompletionUp.mk M S E W R D A H C P N)
      rw [locatedCompletion_decode_encode M,
        locatedCompletion_decode_encode S,
        locatedCompletion_decode_encode E,
        locatedCompletion_decode_encode W,
        locatedCompletion_decode_encode R,
        locatedCompletion_decode_encode D,
        locatedCompletion_decode_encode A,
        locatedCompletion_decode_encode H,
        locatedCompletion_decode_encode C,
        locatedCompletion_decode_encode P,
        locatedCompletion_decode_encode N]

private theorem locatedCompletionToEventFlow_injective {x y : LocatedCompletionUp} :
    locatedCompletionToEventFlow x = locatedCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionFromEventFlow (locatedCompletionToEventFlow x) =
        locatedCompletionFromEventFlow (locatedCompletionToEventFlow y) :=
    congrArg locatedCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (locatedCompletion_round_trip x).symm
      (Eq.trans hread (locatedCompletion_round_trip y)))

private theorem locatedCompletion_fields_faithful :
    ∀ x y : LocatedCompletionUp, locatedCompletionFields x = locatedCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ S₁ E₁ W₁ R₁ D₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ S₂ E₂ W₂ R₂ D₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedCompletionBHistCarrier : BHistCarrier LocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionToEventFlow
  fromEventFlow := locatedCompletionFromEventFlow

instance locatedCompletionChapterTasteGate : ChapterTasteGate LocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionFromEventFlow (locatedCompletionToEventFlow x) = some x
    exact locatedCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCompletionToEventFlow_injective heq)

instance locatedCompletionFieldFaithful : FieldFaithful LocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCompletionFields
  field_faithful := locatedCompletion_fields_faithful

instance locatedCompletionNontrivial : Nontrivial LocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedCompletionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompletionChapterTasteGate

theorem LocatedCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCompletionDecodeBHist (locatedCompletionEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionUp,
        locatedCompletionFromEventFlow (locatedCompletionToEventFlow x) = some x) ∧
      locatedCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨locatedCompletion_decode_encode, locatedCompletion_round_trip, rfl⟩

end BEDC.Derived.LocatedCompletionUp
