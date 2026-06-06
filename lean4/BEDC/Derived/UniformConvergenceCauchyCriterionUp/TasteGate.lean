import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceCauchyCriterionUp : Type where
  | mk (U M F Q R E H C P N : BHist) : UniformConvergenceCauchyCriterionUp
  deriving DecidableEq

def uniformConvergenceCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformConvergenceCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformConvergenceCauchyCriterionEncodeBHist h

def uniformConvergenceCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformConvergenceCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformConvergenceCauchyCriterionDecodeBHist tail)

private theorem
    UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformConvergenceCauchyCriterionDecodeBHist
          (uniformConvergenceCauchyCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformConvergenceCauchyCriterionFields :
    UniformConvergenceCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceCauchyCriterionUp.mk U M F Q R E H C P N =>
      [U, M, F, Q, R, E, H, C, P, N]

def uniformConvergenceCauchyCriterionToEventFlow :
    UniformConvergenceCauchyCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (uniformConvergenceCauchyCriterionFields x).map
      uniformConvergenceCauchyCriterionEncodeBHist

private def uniformConvergenceCauchyCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformConvergenceCauchyCriterionEventAt index rest

def uniformConvergenceCauchyCriterionFromEventFlow
    (ef : EventFlow) : Option UniformConvergenceCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformConvergenceCauchyCriterionUp.mk
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 0 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 1 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 2 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 3 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 4 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 5 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 6 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 7 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 8 ef))
      (uniformConvergenceCauchyCriterionDecodeBHist
        (uniformConvergenceCauchyCriterionEventAt 9 ef)))

def UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_carrier :
    BHistCarrier UniformConvergenceCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceCauchyCriterionToEventFlow
  fromEventFlow := uniformConvergenceCauchyCriterionFromEventFlow

instance uniformConvergenceCauchyCriterionBHistCarrier :
    BHistCarrier UniformConvergenceCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_carrier

private theorem UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_round_trip
    (x : UniformConvergenceCauchyCriterionUp) :
    uniformConvergenceCauchyCriterionFromEventFlow
        (uniformConvergenceCauchyCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U M F Q R E H C P N =>
      change
        some
            (UniformConvergenceCauchyCriterionUp.mk
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist U))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist M))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist F))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist Q))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist R))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist E))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist H))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist C))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist P))
              (uniformConvergenceCauchyCriterionDecodeBHist
                (uniformConvergenceCauchyCriterionEncodeBHist N))) =
          some (UniformConvergenceCauchyCriterionUp.mk U M F Q R E H C P N)
      rw [
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode U,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode M,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode F,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode Q,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode E,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem
    UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformConvergenceCauchyCriterionUp} :
    uniformConvergenceCauchyCriterionToEventFlow x =
        uniformConvergenceCauchyCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          uniformConvergenceCauchyCriterionFromEventFlow
            (uniformConvergenceCauchyCriterionToEventFlow x) :=
        (UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          uniformConvergenceCauchyCriterionFromEventFlow
            (uniformConvergenceCauchyCriterionToEventFlow y) :=
        congrArg uniformConvergenceCauchyCriterionFromEventFlow hxy
      _ = some y :=
        UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem
    UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : UniformConvergenceCauchyCriterionUp,
      uniformConvergenceCauchyCriterionFields x =
          uniformConvergenceCauchyCriterionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ M₁ F₁ Q₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ M₂ F₂ Q₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

def UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_taste_gate :
    @ChapterTasteGate UniformConvergenceCauchyCriterionUp
      UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformConvergenceCauchyCriterionFromEventFlow
          (uniformConvergenceCauchyCriterionToEventFlow x) =
        some x
    exact UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance uniformConvergenceCauchyCriterionChapterTasteGate :
    ChapterTasteGate UniformConvergenceCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_taste_gate

instance uniformConvergenceCauchyCriterionFieldFaithful :
    FieldFaithful UniformConvergenceCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformConvergenceCauchyCriterionFields
  field_faithful :=
    UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_fields_faithful

instance uniformConvergenceCauchyCriterionNontrivial :
    Nontrivial UniformConvergenceCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformConvergenceCauchyCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      UniformConvergenceCauchyCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment :
    (forall h : BHist,
        uniformConvergenceCauchyCriterionDecodeBHist
            (uniformConvergenceCauchyCriterionEncodeBHist h) =
          h) ∧
      uniformConvergenceCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) ∧
        Nonempty (BHistCarrier UniformConvergenceCauchyCriterionUp) ∧
          Nonempty (ChapterTasteGate UniformConvergenceCauchyCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode, rfl,
      ⟨UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_carrier⟩,
      ⟨UniformConvergenceCauchyCriterionTasteGate_single_carrier_alignment_taste_gate⟩⟩

end BEDC.Derived.UniformConvergenceCauchyCriterionUp
