import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterCompletionUp : Type where
  | mk (C W T R L H K P N : BHist) : CauchyFilterCompletionUp
  deriving DecidableEq

def cauchyFilterCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterCompletionEncodeBHist h

def cauchyFilterCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterCompletionDecodeBHist tail)

private theorem cauchyFilterCompletion_decode_encode :
    forall h : BHist,
      cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterCompletionFields : CauchyFilterCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterCompletionUp.mk C W T R L H K P N => [C, W, T, R, L, H, K, P, N]

def cauchyFilterCompletionToEventFlow : CauchyFilterCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterCompletionFields x).map cauchyFilterCompletionEncodeBHist

private def cauchyFilterCompletionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterCompletionEventAt index rest

def cauchyFilterCompletionFromEventFlow
    (ef : EventFlow) : Option CauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyFilterCompletionUp.mk
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 0 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 1 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 2 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 3 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 4 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 5 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 6 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 7 ef))
      (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEventAt 8 ef)))

private theorem cauchyFilterCompletion_round_trip (x : CauchyFilterCompletionUp) :
    cauchyFilterCompletionFromEventFlow (cauchyFilterCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C W T R L H K P N =>
      change
        some
          (CauchyFilterCompletionUp.mk
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist C))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist W))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist T))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist R))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist L))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist H))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist K))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist P))
            (cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist N))) =
          some (CauchyFilterCompletionUp.mk C W T R L H K P N)
      rw [cauchyFilterCompletion_decode_encode C, cauchyFilterCompletion_decode_encode W,
        cauchyFilterCompletion_decode_encode T, cauchyFilterCompletion_decode_encode R,
        cauchyFilterCompletion_decode_encode L, cauchyFilterCompletion_decode_encode H,
        cauchyFilterCompletion_decode_encode K, cauchyFilterCompletion_decode_encode P,
        cauchyFilterCompletion_decode_encode N]

private theorem cauchyFilterCompletionToEventFlow_injective
    {x y : CauchyFilterCompletionUp} :
    cauchyFilterCompletionToEventFlow x = cauchyFilterCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterCompletionFromEventFlow (cauchyFilterCompletionToEventFlow x) =
        cauchyFilterCompletionFromEventFlow (cauchyFilterCompletionToEventFlow y) :=
    congrArg cauchyFilterCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterCompletion_round_trip x).symm
      (Eq.trans hread (cauchyFilterCompletion_round_trip y)))

private theorem cauchyFilterCompletionFields_faithful :
    forall x y : CauchyFilterCompletionUp,
      cauchyFilterCompletionFields x = cauchyFilterCompletionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ W₁ T₁ R₁ L₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk C₂ W₂ T₂ R₂ L₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyFilterCompletionBHistCarrier : BHistCarrier CauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterCompletionToEventFlow
  fromEventFlow := cauchyFilterCompletionFromEventFlow

instance cauchyFilterCompletionChapterTasteGate :
    ChapterTasteGate CauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyFilterCompletionFromEventFlow (cauchyFilterCompletionToEventFlow x) = some x
    exact cauchyFilterCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterCompletionToEventFlow_injective heq)

instance cauchyFilterCompletionFieldFaithful :
    FieldFaithful CauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterCompletionFields
  field_faithful := cauchyFilterCompletionFields_faithful

instance cauchyFilterCompletionNontrivial : Nontrivial CauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyFilterCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyFilterCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def cauchyFilterCompletionTasteGate : ChapterTasteGate CauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterCompletionChapterTasteGate

theorem CauchyFilterCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyFilterCompletionDecodeBHist (cauchyFilterCompletionEncodeBHist h) = h) ∧
      (forall x : CauchyFilterCompletionUp,
        cauchyFilterCompletionFromEventFlow (cauchyFilterCompletionToEventFlow x) = some x) ∧
        (forall x y : CauchyFilterCompletionUp,
          cauchyFilterCompletionToEventFlow x = cauchyFilterCompletionToEventFlow y ->
            x = y) ∧
          cauchyFilterCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyFilterCompletion_decode_encode
  · constructor
    · exact cauchyFilterCompletion_round_trip
    · constructor
      · intro x y hxy
        exact cauchyFilterCompletionToEventFlow_injective hxy
      · rfl

end BEDC.Derived.CauchyfiltercompletionUp
