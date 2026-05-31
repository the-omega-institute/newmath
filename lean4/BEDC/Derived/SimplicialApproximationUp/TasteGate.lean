import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SimplicialApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SimplicialApproximationUp : Type where
  | mk (K L S V F T B M H C P N : BHist) : SimplicialApproximationUp
  deriving DecidableEq

def simplicialApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: simplicialApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: simplicialApproximationEncodeBHist h

def simplicialApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => simplicialApproximationDecodeBHist tail |> BHist.e0
  | BMark.b1 :: tail => simplicialApproximationDecodeBHist tail |> BHist.e1

private theorem SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def simplicialApproximationFields : SimplicialApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SimplicialApproximationUp.mk K L S V F T B M H C P N =>
      [K, L, S, V, F, T, B, M, H, C, P, N]

def simplicialApproximationToEventFlow : SimplicialApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SimplicialApproximationUp.mk K L S V F T B M H C P N =>
      [[BMark.b0],
        simplicialApproximationEncodeBHist K,
        [BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        simplicialApproximationEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        simplicialApproximationEncodeBHist N]

private def simplicialApproximationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => simplicialApproximationEventAtDefault index rest

def simplicialApproximationFromEventFlow (ef : EventFlow) :
    Option SimplicialApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SimplicialApproximationUp.mk
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 1 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 3 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 5 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 7 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 9 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 11 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 13 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 15 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 17 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 19 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 21 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 23 ef)))

private theorem SimplicialApproximationTasteGate_single_carrier_alignment_round_trip
    (x : SimplicialApproximationUp) :
    simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K L S V F T B M H C P N =>
      change
        some
          (SimplicialApproximationUp.mk
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist K))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist L))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist S))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist V))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist F))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist T))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist B))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist M))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist H))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist C))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist P))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist N))) =
          some (SimplicialApproximationUp.mk K L S V F T B M H C P N)
      rw [SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode K,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode L,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode S,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode V,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode F,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode T,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode B,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode M,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode H,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode C,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode P,
        SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode N]

private theorem SimplicialApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SimplicialApproximationUp} :
    simplicialApproximationToEventFlow x = simplicialApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
        simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow y) :=
    congrArg simplicialApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SimplicialApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SimplicialApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem SimplicialApproximationTasteGate_single_carrier_alignment_fields :
    ∀ x y : SimplicialApproximationUp,
      simplicialApproximationFields x = simplicialApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ L₁ S₁ V₁ F₁ T₁ B₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ L₂ S₂ V₂ F₂ T₂ B₂ M₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance simplicialApproximationBHistCarrier : BHistCarrier SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := simplicialApproximationToEventFlow
  fromEventFlow := simplicialApproximationFromEventFlow

instance simplicialApproximationChapterTasteGate :
    ChapterTasteGate SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change simplicialApproximationFromEventFlow
      (simplicialApproximationToEventFlow x) = some x
    exact SimplicialApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SimplicialApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance simplicialApproximationFieldFaithful :
    FieldFaithful SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := simplicialApproximationFields
  field_faithful := SimplicialApproximationTasteGate_single_carrier_alignment_fields

instance simplicialApproximationNontrivial : Nontrivial SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SimplicialApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SimplicialApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def SimplicialApproximationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SimplicialApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  simplicialApproximationChapterTasteGate

theorem SimplicialApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SimplicialApproximationUp) ∧
      Nonempty (FieldFaithful SimplicialApproximationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial SimplicialApproximationUp) ∧
      (∀ h : BHist,
        simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist h) = h) ∧
      (∀ x : SimplicialApproximationUp,
        simplicialApproximationFromEventFlow
          (simplicialApproximationToEventFlow x) = some x) ∧
      simplicialApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨simplicialApproximationChapterTasteGate⟩
  · constructor
    · exact ⟨simplicialApproximationFieldFaithful⟩
    · constructor
      · exact ⟨simplicialApproximationNontrivial⟩
      · constructor
        · exact SimplicialApproximationTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact SimplicialApproximationTasteGate_single_carrier_alignment_round_trip
          · rfl

end BEDC.Derived.SimplicialApproximationUp
