import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyConvexCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyConvexCompletionUp : Type where
  | mk (X S F U E H C P N : BHist) : LocallyConvexCompletionUp
  deriving DecidableEq

def locallyConvexCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyConvexCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyConvexCompletionEncodeBHist h

def locallyConvexCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyConvexCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyConvexCompletionDecodeBHist tail)

private theorem locallyConvexCompletionDecode_encode :
    ∀ h : BHist,
      locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locallyConvexCompletionFields : LocallyConvexCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyConvexCompletionUp.mk X S F U E H C P N => [X, S, F, U, E, H, C, P, N]

def locallyConvexCompletionToEventFlow : LocallyConvexCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locallyConvexCompletionFields x).map locallyConvexCompletionEncodeBHist

private def locallyConvexCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locallyConvexCompletionEventAt index rest

def locallyConvexCompletionFromEventFlow :
    EventFlow → Option LocallyConvexCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocallyConvexCompletionUp.mk
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 0 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 1 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 2 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 3 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 4 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 5 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 6 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 7 ef))
        (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEventAt 8 ef)))

private theorem locallyConvexCompletion_round_trip :
    ∀ x : LocallyConvexCompletionUp,
      locallyConvexCompletionFromEventFlow (locallyConvexCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S F U E H C P N =>
      change
        some
            (LocallyConvexCompletionUp.mk
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist X))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist S))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist F))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist U))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist E))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist H))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist C))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist P))
              (locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist N))) =
          some (LocallyConvexCompletionUp.mk X S F U E H C P N)
      rw [locallyConvexCompletionDecode_encode X, locallyConvexCompletionDecode_encode S,
        locallyConvexCompletionDecode_encode F, locallyConvexCompletionDecode_encode U,
        locallyConvexCompletionDecode_encode E, locallyConvexCompletionDecode_encode H,
        locallyConvexCompletionDecode_encode C, locallyConvexCompletionDecode_encode P,
        locallyConvexCompletionDecode_encode N]

private theorem locallyConvexCompletionToEventFlow_injective
    {x y : LocallyConvexCompletionUp} :
    locallyConvexCompletionToEventFlow x = locallyConvexCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locallyConvexCompletionFromEventFlow (locallyConvexCompletionToEventFlow x) =
        locallyConvexCompletionFromEventFlow (locallyConvexCompletionToEventFlow y) :=
    congrArg locallyConvexCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locallyConvexCompletion_round_trip x).symm
      (Eq.trans hread (locallyConvexCompletion_round_trip y)))

private theorem locallyConvexCompletionFieldFaithfulProof :
    ∀ x y : LocallyConvexCompletionUp,
      locallyConvexCompletionFields x = locallyConvexCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ S₁ F₁ U₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ S₂ F₂ U₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locallyConvexCompletionBHistCarrier : BHistCarrier LocallyConvexCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locallyConvexCompletionToEventFlow
  fromEventFlow := locallyConvexCompletionFromEventFlow

instance locallyConvexCompletionChapterTasteGate :
    ChapterTasteGate LocallyConvexCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locallyConvexCompletionFromEventFlow (locallyConvexCompletionToEventFlow x) =
      some x
    exact locallyConvexCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locallyConvexCompletionToEventFlow_injective heq)

instance locallyConvexCompletionFieldFaithful :
    FieldFaithful LocallyConvexCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locallyConvexCompletionFields
  field_faithful := locallyConvexCompletionFieldFaithfulProof

instance locallyConvexCompletionNontrivial : Nontrivial LocallyConvexCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocallyConvexCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocallyConvexCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocallyConvexCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locallyConvexCompletionChapterTasteGate

theorem LocallyConvexCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locallyConvexCompletionDecodeBHist (locallyConvexCompletionEncodeBHist h) = h) ∧
      (∀ x : LocallyConvexCompletionUp,
        locallyConvexCompletionFromEventFlow (locallyConvexCompletionToEventFlow x) = some x) ∧
      (∀ x y : LocallyConvexCompletionUp,
        locallyConvexCompletionToEventFlow x = locallyConvexCompletionToEventFlow y → x = y) ∧
      locallyConvexCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨locallyConvexCompletionDecode_encode,
      locallyConvexCompletion_round_trip,
      (fun _ _ heq => locallyConvexCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocallyConvexCompletionUp
