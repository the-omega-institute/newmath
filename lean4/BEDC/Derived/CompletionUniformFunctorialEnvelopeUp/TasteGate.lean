import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionUniformFunctorialEnvelopeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionUniformFunctorialEnvelopeUp : Type where
  | mk (U M F L S R A H C P N : BHist) : CompletionUniformFunctorialEnvelopeUp
  deriving DecidableEq

def completionUniformFunctorialEnvelopeEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionUniformFunctorialEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionUniformFunctorialEnvelopeEncodeBHist h

def completionUniformFunctorialEnvelopeDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionUniformFunctorialEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionUniformFunctorialEnvelopeDecodeBHist tail)

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionUniformFunctorialEnvelopeDecodeBHist
          (completionUniformFunctorialEnvelopeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionUniformFunctorialEnvelopeFields :
    CompletionUniformFunctorialEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionUniformFunctorialEnvelopeUp.mk U M F L S R A H C P N =>
      [U, M, F, L, S, R, A, H, C, P, N]

def completionUniformFunctorialEnvelopeToEventFlow :
    CompletionUniformFunctorialEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (completionUniformFunctorialEnvelopeFields x).map
        completionUniformFunctorialEnvelopeEncodeBHist

private def completionUniformFunctorialEnvelopeEventAt : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionUniformFunctorialEnvelopeEventAt index rest

def completionUniformFunctorialEnvelopeFromEventFlow
    (ef : EventFlow) : Option CompletionUniformFunctorialEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionUniformFunctorialEnvelopeUp.mk
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 0 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 1 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 2 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 3 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 4 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 5 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 6 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 7 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 8 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 9 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAt 10 ef)))

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip
    (x : CompletionUniformFunctorialEnvelopeUp) :
    completionUniformFunctorialEnvelopeFromEventFlow
        (completionUniformFunctorialEnvelopeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U M F L S R A H C P N =>
      change
        some
          (CompletionUniformFunctorialEnvelopeUp.mk
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist U))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist M))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist F))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist L))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist S))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist R))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist A))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist H))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist C))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist P))
            (completionUniformFunctorialEnvelopeDecodeBHist
              (completionUniformFunctorialEnvelopeEncodeBHist N))) =
          some (CompletionUniformFunctorialEnvelopeUp.mk U M F L S R A H C P N)
      rw [CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode U,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode M,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode F,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode L,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode S,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode R,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode A,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode H,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode C,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode P,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode N]

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_injective
    {x y : CompletionUniformFunctorialEnvelopeUp} :
    completionUniformFunctorialEnvelopeToEventFlow x =
        completionUniformFunctorialEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionUniformFunctorialEnvelopeFromEventFlow
          (completionUniformFunctorialEnvelopeToEventFlow x) =
        completionUniformFunctorialEnvelopeFromEventFlow
          (completionUniformFunctorialEnvelopeToEventFlow y) :=
    congrArg completionUniformFunctorialEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompletionUniformFunctorialEnvelopeUp,
      completionUniformFunctorialEnvelopeFields x =
          completionUniformFunctorialEnvelopeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ M₁ F₁ L₁ S₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ M₂ F₂ L₂ S₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance completionUniformFunctorialEnvelopeBHistCarrier :
    BHistCarrier CompletionUniformFunctorialEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionUniformFunctorialEnvelopeToEventFlow
  fromEventFlow := completionUniformFunctorialEnvelopeFromEventFlow

instance completionUniformFunctorialEnvelopeChapterTasteGate :
    ChapterTasteGate CompletionUniformFunctorialEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completionUniformFunctorialEnvelopeFromEventFlow
          (completionUniformFunctorialEnvelopeToEventFlow x) =
        some x
    exact CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_injective heq)

instance completionUniformFunctorialEnvelopeFieldFaithful :
    FieldFaithful CompletionUniformFunctorialEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionUniformFunctorialEnvelopeFields
  field_faithful := CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate CompletionUniformFunctorialEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUniformFunctorialEnvelopeChapterTasteGate

def taste_gate_witness : FieldFaithful CompletionUniformFunctorialEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUniformFunctorialEnvelopeFieldFaithful

theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      completionUniformFunctorialEnvelopeDecodeBHist
          (completionUniformFunctorialEnvelopeEncodeBHist h) =
        h) ∧
      (∀ x : CompletionUniformFunctorialEnvelopeUp,
        completionUniformFunctorialEnvelopeFromEventFlow
            (completionUniformFunctorialEnvelopeToEventFlow x) =
          some x) ∧
        (∀ x y : CompletionUniformFunctorialEnvelopeUp,
          completionUniformFunctorialEnvelopeToEventFlow x =
              completionUniformFunctorialEnvelopeToEventFlow y →
            x = y) ∧
          completionUniformFunctorialEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode
  constructor
  · exact CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.CompletionUniformFunctorialEnvelopeUp.TasteGate
