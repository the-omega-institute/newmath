import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICPiAdequacyBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICPiAdequacyBudgetUp : Type where
  | mk (G Pi N A S F O H C P L : BHist) : MetaCICPiAdequacyBudgetUp
  deriving DecidableEq

def metaCICPiAdequacyBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICPiAdequacyBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICPiAdequacyBudgetEncodeBHist h

def metaCICPiAdequacyBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICPiAdequacyBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICPiAdequacyBudgetDecodeBHist tail)

private theorem metaCICPiAdequacyBudget_decode_encode_bhist :
    ∀ h : BHist,
      metaCICPiAdequacyBudgetDecodeBHist
        (metaCICPiAdequacyBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICPiAdequacyBudgetFields :
    MetaCICPiAdequacyBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICPiAdequacyBudgetUp.mk G Pi N A S F O H C P L =>
      [G, Pi, N, A, S, F, O, H, C, P, L]

def metaCICPiAdequacyBudgetToEventFlow :
    MetaCICPiAdequacyBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map metaCICPiAdequacyBudgetEncodeBHist
        (metaCICPiAdequacyBudgetFields x)

def metaCICPiAdequacyBudgetFromEventFlow :
    EventFlow → Option MetaCICPiAdequacyBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [G, Pi, N, A, S, F, O, H, C, P, L] =>
      some
        (MetaCICPiAdequacyBudgetUp.mk
          (metaCICPiAdequacyBudgetDecodeBHist G)
          (metaCICPiAdequacyBudgetDecodeBHist Pi)
          (metaCICPiAdequacyBudgetDecodeBHist N)
          (metaCICPiAdequacyBudgetDecodeBHist A)
          (metaCICPiAdequacyBudgetDecodeBHist S)
          (metaCICPiAdequacyBudgetDecodeBHist F)
          (metaCICPiAdequacyBudgetDecodeBHist O)
          (metaCICPiAdequacyBudgetDecodeBHist H)
          (metaCICPiAdequacyBudgetDecodeBHist C)
          (metaCICPiAdequacyBudgetDecodeBHist P)
          (metaCICPiAdequacyBudgetDecodeBHist L))
  | _ => none

private theorem metaCICPiAdequacyBudget_round_trip :
    ∀ x : MetaCICPiAdequacyBudgetUp,
      metaCICPiAdequacyBudgetFromEventFlow
        (metaCICPiAdequacyBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G Pi N A S F O H C P L =>
      simp only [metaCICPiAdequacyBudgetToEventFlow,
        metaCICPiAdequacyBudgetFields, List.map_cons, List.map_nil,
        metaCICPiAdequacyBudgetFromEventFlow,
        metaCICPiAdequacyBudget_decode_encode_bhist]

private theorem metaCICPiAdequacyBudgetToEventFlow_injective
    {x y : MetaCICPiAdequacyBudgetUp} :
    metaCICPiAdequacyBudgetToEventFlow x =
        metaCICPiAdequacyBudgetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICPiAdequacyBudgetFromEventFlow
          (metaCICPiAdequacyBudgetToEventFlow x) =
        metaCICPiAdequacyBudgetFromEventFlow
          (metaCICPiAdequacyBudgetToEventFlow y) :=
    congrArg metaCICPiAdequacyBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICPiAdequacyBudget_round_trip x).symm
      (Eq.trans hread (metaCICPiAdequacyBudget_round_trip y)))

private theorem metaCICPiAdequacyBudget_field_faithful :
    ∀ x y : MetaCICPiAdequacyBudgetUp,
      metaCICPiAdequacyBudgetFields x = metaCICPiAdequacyBudgetFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk G₁ Pi₁ N₁ A₁ S₁ F₁ O₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk G₂ Pi₂ N₂ A₂ S₂ F₂ O₂ H₂ C₂ P₂ L₂ =>
          cases h
          rfl

instance metaCICPiAdequacyBudgetBHistCarrier :
    BHistCarrier MetaCICPiAdequacyBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICPiAdequacyBudgetToEventFlow
  fromEventFlow := metaCICPiAdequacyBudgetFromEventFlow

instance metaCICPiAdequacyBudgetChapterTasteGate :
    ChapterTasteGate MetaCICPiAdequacyBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICPiAdequacyBudgetFromEventFlow
        (metaCICPiAdequacyBudgetToEventFlow x) = some x
    exact metaCICPiAdequacyBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICPiAdequacyBudgetToEventFlow_injective heq)

instance metaCICPiAdequacyBudgetFieldFaithful :
    FieldFaithful MetaCICPiAdequacyBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICPiAdequacyBudgetFields
  field_faithful := metaCICPiAdequacyBudget_field_faithful

instance metaCICPiAdequacyBudgetNontrivial :
    Nontrivial MetaCICPiAdequacyBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICPiAdequacyBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICPiAdequacyBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICPiAdequacyBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICPiAdequacyBudgetChapterTasteGate

theorem MetaCICPiAdequacyBudgetTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metaCICPiAdequacyBudgetDecodeBHist
        (metaCICPiAdequacyBudgetEncodeBHist h) = h) ∧
      (forall x : MetaCICPiAdequacyBudgetUp,
        metaCICPiAdequacyBudgetFromEventFlow
          (metaCICPiAdequacyBudgetToEventFlow x) = some x) ∧
        (forall x y : MetaCICPiAdequacyBudgetUp,
          metaCICPiAdequacyBudgetToEventFlow x =
              metaCICPiAdequacyBudgetToEventFlow y →
            x = y) ∧
          metaCICPiAdequacyBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICPiAdequacyBudget_decode_encode_bhist
  · constructor
    · exact metaCICPiAdequacyBudget_round_trip
    · constructor
      · intro x y heq
        exact metaCICPiAdequacyBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICPiAdequacyBudgetUp
