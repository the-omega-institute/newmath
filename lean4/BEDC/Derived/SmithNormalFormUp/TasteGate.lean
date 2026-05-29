import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SmithNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SmithNormalFormUp : Type where
  | mk (M R C D V E U H T P N : BHist) : SmithNormalFormUp
  deriving DecidableEq

def smithNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: smithNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: smithNormalFormEncodeBHist h

def smithNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (smithNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (smithNormalFormDecodeBHist tail)

private theorem smithNormalFormDecodeEncodeBHist :
    ∀ h : BHist, smithNormalFormDecodeBHist (smithNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def smithNormalFormFields : SmithNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SmithNormalFormUp.mk M R C D V E U H T P N => [M, R, C, D, V, E, U, H, T, P, N]

def smithNormalFormToEventFlow : SmithNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (smithNormalFormFields x).map smithNormalFormEncodeBHist

private def smithNormalFormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => smithNormalFormEventAt index rest

def smithNormalFormFromEventFlow (ef : EventFlow) : Option SmithNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SmithNormalFormUp.mk
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 0 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 1 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 2 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 3 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 4 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 5 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 6 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 7 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 8 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 9 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAt 10 ef)))

private theorem smithNormalForm_round_trip (x : SmithNormalFormUp) :
    smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M R C D V E U H T P N =>
      change
        some
          (SmithNormalFormUp.mk
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist M))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist R))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist C))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist D))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist V))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist E))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist U))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist H))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist T))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist P))
            (smithNormalFormDecodeBHist (smithNormalFormEncodeBHist N))) =
          some (SmithNormalFormUp.mk M R C D V E U H T P N)
      rw [smithNormalFormDecodeEncodeBHist M,
        smithNormalFormDecodeEncodeBHist R,
        smithNormalFormDecodeEncodeBHist C,
        smithNormalFormDecodeEncodeBHist D,
        smithNormalFormDecodeEncodeBHist V,
        smithNormalFormDecodeEncodeBHist E,
        smithNormalFormDecodeEncodeBHist U,
        smithNormalFormDecodeEncodeBHist H,
        smithNormalFormDecodeEncodeBHist T,
        smithNormalFormDecodeEncodeBHist P,
        smithNormalFormDecodeEncodeBHist N]

private theorem smithNormalFormToEventFlow_injective {x y : SmithNormalFormUp} :
    smithNormalFormToEventFlow x = smithNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) =
        smithNormalFormFromEventFlow (smithNormalFormToEventFlow y) :=
    congrArg smithNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (smithNormalForm_round_trip x).symm
      (Eq.trans hread (smithNormalForm_round_trip y)))

private theorem smithNormalForm_fields_faithful :
    ∀ x y : SmithNormalFormUp, smithNormalFormFields x = smithNormalFormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ R₁ C₁ D₁ V₁ E₁ U₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk M₂ R₂ C₂ D₂ V₂ E₂ U₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance smithNormalFormBHistCarrier : BHistCarrier SmithNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := smithNormalFormToEventFlow
  fromEventFlow := smithNormalFormFromEventFlow

instance smithNormalFormChapterTasteGate : ChapterTasteGate SmithNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) = some x
    exact smithNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (smithNormalFormToEventFlow_injective heq)

instance smithNormalFormFieldFaithful : FieldFaithful SmithNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := smithNormalFormFields
  field_faithful := smithNormalForm_fields_faithful

instance smithNormalFormNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SmithNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SmithNormalFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SmithNormalFormUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SmithNormalFormUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SmithNormalFormUp) ∧
      Nonempty (FieldFaithful SmithNormalFormUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SmithNormalFormUp) ∧
          (∀ h : BHist, smithNormalFormDecodeBHist (smithNormalFormEncodeBHist h) = h) ∧
            (∀ x : SmithNormalFormUp,
              smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) = some x) ∧
              (∀ x y : SmithNormalFormUp,
                smithNormalFormToEventFlow x = smithNormalFormToEventFlow y → x = y) ∧
                smithNormalFormEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨smithNormalFormChapterTasteGate⟩,
      ⟨smithNormalFormFieldFaithful⟩,
      ⟨smithNormalFormNontrivial⟩,
      smithNormalFormDecodeEncodeBHist,
      smithNormalForm_round_trip,
      (fun _ _ heq => smithNormalFormToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SmithNormalFormUp
