import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDifferenceCriterionUp : Type where
  | mk (X Y D Z Q W T E H C P N : BHist) : CauchyDifferenceCriterionUp
  deriving DecidableEq

def cauchyDifferenceCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDifferenceCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDifferenceCriterionEncodeBHist h

def cauchyDifferenceCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDifferenceCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDifferenceCriterionDecodeBHist tail)

private theorem CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyDifferenceCriterionFields : CauchyDifferenceCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N =>
      [X, Y, D, Z, Q, W, T, E, H, C, P, N]

def cauchyDifferenceCriterionToEventFlow : CauchyDifferenceCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyDifferenceCriterionFields x).map cauchyDifferenceCriterionEncodeBHist

private def cauchyDifferenceCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyDifferenceCriterionEventAt index rest

def cauchyDifferenceCriterionFromEventFlow (ef : EventFlow) :
    Option CauchyDifferenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyDifferenceCriterionUp.mk
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 0 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 1 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 2 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 3 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 4 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 5 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 6 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 7 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 8 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 9 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 10 ef))
      (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEventAt 11 ef)))

private theorem CauchyDifferenceCriterionTasteGate_single_carrier_alignment_round_trip
    (x : CauchyDifferenceCriterionUp) :
    cauchyDifferenceCriterionFromEventFlow (cauchyDifferenceCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y D Z Q W T E H C P N =>
      change
        some
          (CauchyDifferenceCriterionUp.mk
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist X))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist Y))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist D))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist Z))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist Q))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist W))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist T))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist E))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist H))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist C))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist P))
            (cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist N))) =
          some (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N)
      rw [CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode X,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode Y,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode T,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyDifferenceCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyDifferenceCriterionUp} :
    cauchyDifferenceCriterionToEventFlow x = cauchyDifferenceCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDifferenceCriterionFromEventFlow (cauchyDifferenceCriterionToEventFlow x) =
        cauchyDifferenceCriterionFromEventFlow (cauchyDifferenceCriterionToEventFlow y) :=
    congrArg cauchyDifferenceCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyDifferenceCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyDifferenceCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyDifferenceCriterionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyDifferenceCriterionUp,
      cauchyDifferenceCriterionFields x = cauchyDifferenceCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ D₁ Z₁ Q₁ W₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ D₂ Z₂ Q₂ W₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyDifferenceCriterionBHistCarrier :
    BHistCarrier CauchyDifferenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDifferenceCriterionToEventFlow
  fromEventFlow := cauchyDifferenceCriterionFromEventFlow

instance cauchyDifferenceCriterionChapterTasteGate :
    ChapterTasteGate CauchyDifferenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDifferenceCriterionFromEventFlow (cauchyDifferenceCriterionToEventFlow x) =
      some x
    exact CauchyDifferenceCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyDifferenceCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyDifferenceCriterionFieldFaithful :
    FieldFaithful CauchyDifferenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyDifferenceCriterionFields
  field_faithful := CauchyDifferenceCriterionTasteGate_single_carrier_alignment_field_faithful

instance cauchyDifferenceCriterionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyDifferenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyDifferenceCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyDifferenceCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyDifferenceCriterionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyDifferenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDifferenceCriterionChapterTasteGate

theorem CauchyDifferenceCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyDifferenceCriterionDecodeBHist (cauchyDifferenceCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyDifferenceCriterionUp,
        cauchyDifferenceCriterionFromEventFlow (cauchyDifferenceCriterionToEventFlow x) = some x) ∧
      (∀ x y : CauchyDifferenceCriterionUp,
        cauchyDifferenceCriterionToEventFlow x = cauchyDifferenceCriterionToEventFlow y → x = y) ∧
      cauchyDifferenceCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyDifferenceCriterionTasteGate_single_carrier_alignment_decode_encode,
      CauchyDifferenceCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyDifferenceCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
