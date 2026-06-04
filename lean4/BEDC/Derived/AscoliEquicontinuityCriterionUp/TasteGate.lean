import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AscoliEquicontinuityCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AscoliEquicontinuityCriterionUp : Type where
  | mk (K E U F M H C P N : BHist) : AscoliEquicontinuityCriterionUp

def ascoliEquicontinuityCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ascoliEquicontinuityCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ascoliEquicontinuityCriterionEncodeBHist h

def ascoliEquicontinuityCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ascoliEquicontinuityCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ascoliEquicontinuityCriterionDecodeBHist tail)

private theorem AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      ascoliEquicontinuityCriterionDecodeBHist
        (ascoliEquicontinuityCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ascoliEquicontinuityCriterionFields :
    AscoliEquicontinuityCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AscoliEquicontinuityCriterionUp.mk K E U F M H C P N =>
      [K, E, U, F, M, H, C, P, N]

def ascoliEquicontinuityCriterionToEventFlow :
    AscoliEquicontinuityCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ascoliEquicontinuityCriterionFields x).map
        ascoliEquicontinuityCriterionEncodeBHist

private def ascoliEquicontinuityCriterionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ascoliEquicontinuityCriterionEventAtDefault index rest

def ascoliEquicontinuityCriterionFromEventFlow :
    EventFlow → Option AscoliEquicontinuityCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (AscoliEquicontinuityCriterionUp.mk
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 0 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 1 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 2 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 3 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 4 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 5 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 6 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 7 ef))
          (ascoliEquicontinuityCriterionDecodeBHist
            (ascoliEquicontinuityCriterionEventAtDefault 8 ef)))

private theorem AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AscoliEquicontinuityCriterionUp,
      ascoliEquicontinuityCriterionFromEventFlow
        (ascoliEquicontinuityCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K E U F M H C P N =>
      change
        some
          (AscoliEquicontinuityCriterionUp.mk
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist K))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist E))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist U))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist F))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist M))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist H))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist C))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist P))
            (ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist N))) =
          some (AscoliEquicontinuityCriterionUp.mk K E U F M H C P N)
      rw [AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode K,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode E,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode U,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode F,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode M,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode H,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode C,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode P,
        AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode N]

private theorem ascoliEquicontinuityCriterionToEventFlow_injective
    {x y : AscoliEquicontinuityCriterionUp} :
    ascoliEquicontinuityCriterionToEventFlow x =
      ascoliEquicontinuityCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ascoliEquicontinuityCriterionFromEventFlow
          (ascoliEquicontinuityCriterionToEventFlow x) =
        ascoliEquicontinuityCriterionFromEventFlow
          (ascoliEquicontinuityCriterionToEventFlow y) :=
    congrArg ascoliEquicontinuityCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ascoliEquicontinuityCriterion_fields_faithful :
    ∀ x y : AscoliEquicontinuityCriterionUp,
      ascoliEquicontinuityCriterionFields x =
        ascoliEquicontinuityCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ E₁ U₁ F₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ E₂ U₂ F₂ M₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance ascoliEquicontinuityCriterionBHistCarrier :
    BHistCarrier AscoliEquicontinuityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ascoliEquicontinuityCriterionToEventFlow
  fromEventFlow := ascoliEquicontinuityCriterionFromEventFlow

instance ascoliEquicontinuityCriterionChapterTasteGate :
    ChapterTasteGate AscoliEquicontinuityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ascoliEquicontinuityCriterionFromEventFlow
        (ascoliEquicontinuityCriterionToEventFlow x) = some x
    exact AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ascoliEquicontinuityCriterionToEventFlow_injective heq)

instance ascoliEquicontinuityCriterionFieldFaithful :
    FieldFaithful AscoliEquicontinuityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ascoliEquicontinuityCriterionFields
  field_faithful := ascoliEquicontinuityCriterion_fields_faithful

instance ascoliEquicontinuityCriterionNontrivial :
    Nontrivial AscoliEquicontinuityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AscoliEquicontinuityCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AscoliEquicontinuityCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AscoliEquicontinuityCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ascoliEquicontinuityCriterionChapterTasteGate

theorem AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AscoliEquicontinuityCriterionUp) ∧
      Nonempty (FieldFaithful AscoliEquicontinuityCriterionUp) ∧
        Nonempty (Nontrivial AscoliEquicontinuityCriterionUp) ∧
          (∀ h : BHist,
            ascoliEquicontinuityCriterionDecodeBHist
              (ascoliEquicontinuityCriterionEncodeBHist h) = h) ∧
            (∀ x : AscoliEquicontinuityCriterionUp,
              ascoliEquicontinuityCriterionFromEventFlow
                (ascoliEquicontinuityCriterionToEventFlow x) = some x) ∧
              (∀ x y : AscoliEquicontinuityCriterionUp,
                ascoliEquicontinuityCriterionToEventFlow x =
                    ascoliEquicontinuityCriterionToEventFlow y →
                  x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨ascoliEquicontinuityCriterionChapterTasteGate⟩,
      ⟨ascoliEquicontinuityCriterionFieldFaithful⟩,
      ⟨ascoliEquicontinuityCriterionNontrivial⟩,
      AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_decode,
      AscoliEquicontinuityCriterionTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => ascoliEquicontinuityCriterionToEventFlow_injective heq⟩

end BEDC.Derived.AscoliEquicontinuityCriterionUp
