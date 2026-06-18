import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCriterionUniformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCriterionUniformUp : Type where
  | mk (S D R E M H C P N : BHist) : CauchyCriterionUniformUp
  deriving DecidableEq

def cauchyCriterionUniformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCriterionUniformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCriterionUniformEncodeBHist h

def cauchyCriterionUniformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCriterionUniformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCriterionUniformDecodeBHist tail)

private theorem CauchyCriterionUniformTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCriterionUniformFields : CauchyCriterionUniformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCriterionUniformUp.mk S D R E M H C P N => [S, D, R, E, M, H, C, P, N]

def cauchyCriterionUniformToEventFlow : CauchyCriterionUniformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCriterionUniformFields x).map cauchyCriterionUniformEncodeBHist

private def cauchyCriterionUniformEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCriterionUniformEventAtDefault index rest

def cauchyCriterionUniformFromEventFlow : EventFlow → Option CauchyCriterionUniformUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyCriterionUniformUp.mk
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 0 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 1 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 2 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 3 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 4 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 5 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 6 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 7 ef))
          (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEventAtDefault 8 ef)))

private theorem CauchyCriterionUniformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCriterionUniformUp,
      cauchyCriterionUniformFromEventFlow (cauchyCriterionUniformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R E M H C P N =>
      change
        some
          (CauchyCriterionUniformUp.mk
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist S))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist D))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist R))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist E))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist M))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist H))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist C))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist P))
            (cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist N))) =
          some (CauchyCriterionUniformUp.mk S D R E M H C P N)
      rw [CauchyCriterionUniformTasteGate_single_carrier_alignment_decode S,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode D,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode R,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode E,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode M,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode H,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode C,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode P,
        CauchyCriterionUniformTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCriterionUniformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCriterionUniformUp} :
    cauchyCriterionUniformToEventFlow x = cauchyCriterionUniformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCriterionUniformFromEventFlow (cauchyCriterionUniformToEventFlow x) =
        cauchyCriterionUniformFromEventFlow (cauchyCriterionUniformToEventFlow y) :=
    congrArg cauchyCriterionUniformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCriterionUniformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyCriterionUniformTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCriterionUniformTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyCriterionUniformUp,
      cauchyCriterionUniformFields x = cauchyCriterionUniformFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ D₁ R₁ E₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ D₂ R₂ E₂ M₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyCriterionUniformBHistCarrier : BHistCarrier CauchyCriterionUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCriterionUniformToEventFlow
  fromEventFlow := cauchyCriterionUniformFromEventFlow

instance cauchyCriterionUniformChapterTasteGate :
    ChapterTasteGate CauchyCriterionUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCriterionUniformFromEventFlow (cauchyCriterionUniformToEventFlow x) = some x
    exact CauchyCriterionUniformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCriterionUniformTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCriterionUniformFieldFaithful : FieldFaithful CauchyCriterionUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCriterionUniformFields
  field_faithful := CauchyCriterionUniformTasteGate_single_carrier_alignment_fields

instance cauchyCriterionUniformNontrivial : Nontrivial CauchyCriterionUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCriterionUniformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCriterionUniformUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCriterionUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCriterionUniformChapterTasteGate

theorem CauchyCriterionUniformTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCriterionUniformDecodeBHist (cauchyCriterionUniformEncodeBHist h) = h) ∧
      (∀ x : CauchyCriterionUniformUp,
        cauchyCriterionUniformFromEventFlow (cauchyCriterionUniformToEventFlow x) = some x) ∧
        (∀ x y : CauchyCriterionUniformUp,
          cauchyCriterionUniformToEventFlow x = cauchyCriterionUniformToEventFlow y → x = y) ∧
          cauchyCriterionUniformEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CauchyCriterionUniformTasteGate_single_carrier_alignment_decode,
      CauchyCriterionUniformTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCriterionUniformTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCriterionUniformUp
