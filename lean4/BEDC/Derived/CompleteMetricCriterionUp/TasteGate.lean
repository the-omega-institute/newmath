import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteMetricCriterionUp : Type where
  | mk (C W T R M L H K0 P N : BHist) : CompleteMetricCriterionUp
  deriving DecidableEq

def completeMetricCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeMetricCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeMetricCriterionEncodeBHist h

def completeMetricCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeMetricCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeMetricCriterionDecodeBHist tail)

private theorem completeMetricCriterionDecodeEncode :
    ∀ h : BHist,
      completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeMetricCriterionFields : CompleteMetricCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricCriterionUp.mk C W T R M L H K0 P N => [C, W, T, R, M, L, H, K0, P, N]

def completeMetricCriterionToEventFlow : CompleteMetricCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completeMetricCriterionFields x).map completeMetricCriterionEncodeBHist

private def completeMetricCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completeMetricCriterionEventAtDefault index rest

def completeMetricCriterionFromEventFlow
    (ef : EventFlow) : Option CompleteMetricCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteMetricCriterionUp.mk
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 0 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 1 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 2 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 3 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 4 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 5 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 6 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 7 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 8 ef))
      (completeMetricCriterionDecodeBHist (completeMetricCriterionEventAtDefault 9 ef)))

private theorem completeMetricCriterion_round_trip :
    ∀ x : CompleteMetricCriterionUp,
      completeMetricCriterionFromEventFlow (completeMetricCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C W T R M L H K0 P N =>
      change
        some
          (CompleteMetricCriterionUp.mk
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist C))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist W))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist T))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist R))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist M))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist L))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist H))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist K0))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist P))
            (completeMetricCriterionDecodeBHist (completeMetricCriterionEncodeBHist N))) =
          some (CompleteMetricCriterionUp.mk C W T R M L H K0 P N)
      rw [completeMetricCriterionDecodeEncode C, completeMetricCriterionDecodeEncode W,
        completeMetricCriterionDecodeEncode T, completeMetricCriterionDecodeEncode R,
        completeMetricCriterionDecodeEncode M, completeMetricCriterionDecodeEncode L,
        completeMetricCriterionDecodeEncode H, completeMetricCriterionDecodeEncode K0,
        completeMetricCriterionDecodeEncode P, completeMetricCriterionDecodeEncode N]

private theorem completeMetricCriterionToEventFlow_injective
    {x y : CompleteMetricCriterionUp} :
    completeMetricCriterionToEventFlow x = completeMetricCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeMetricCriterionFromEventFlow (completeMetricCriterionToEventFlow x) =
        completeMetricCriterionFromEventFlow (completeMetricCriterionToEventFlow y) :=
    congrArg completeMetricCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeMetricCriterion_round_trip x).symm
      (Eq.trans hread (completeMetricCriterion_round_trip y)))

private theorem completeMetricCriterionFieldFaithfulProof :
    ∀ x y : CompleteMetricCriterionUp,
      completeMetricCriterionFields x = completeMetricCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk C₁ W₁ T₁ R₁ M₁ L₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk C₂ W₂ T₂ R₂ M₂ L₂ H₂ K₂ P₂ N₂ =>
          change [C₁, W₁, T₁, R₁, M₁, L₁, H₁, K₁, P₁, N₁] =
            [C₂, W₂, T₂, R₂, M₂, L₂, H₂, K₂, P₂, N₂] at h
          cases h
          rfl

instance completeMetricCriterionBHistCarrier :
    BHistCarrier CompleteMetricCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeMetricCriterionToEventFlow
  fromEventFlow := completeMetricCriterionFromEventFlow

instance completeMetricCriterionChapterTasteGate :
    ChapterTasteGate CompleteMetricCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeMetricCriterionFromEventFlow (completeMetricCriterionToEventFlow x) = some x
    exact completeMetricCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeMetricCriterionToEventFlow_injective heq)

instance completeMetricCriterionFieldFaithful :
    FieldFaithful CompleteMetricCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completeMetricCriterionFields
  field_faithful := completeMetricCriterionFieldFaithfulProof

instance completeMetricCriterionNontrivial :
    Nontrivial CompleteMetricCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompleteMetricCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompleteMetricCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompleteMetricCriterionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompleteMetricCriterionUp) ∧
      Nonempty (ChapterTasteGate CompleteMetricCriterionUp) ∧
        Nonempty (FieldFaithful CompleteMetricCriterionUp) ∧
          Nonempty (Nontrivial CompleteMetricCriterionUp) ∧
            completeMetricCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨completeMetricCriterionBHistCarrier⟩,
      ⟨completeMetricCriterionChapterTasteGate⟩,
      ⟨completeMetricCriterionFieldFaithful⟩,
      ⟨completeMetricCriterionNontrivial⟩,
      rfl⟩

end BEDC.Derived.CompleteMetricCriterionUp
