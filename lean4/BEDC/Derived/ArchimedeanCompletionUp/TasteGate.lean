import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanCompletionUp : Type where
  | mk (F K R D O E H C P N : BHist) : ArchimedeanCompletionUp
  deriving DecidableEq

def archimedeanCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanCompletionEncodeBHist h

def archimedeanCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanCompletionDecodeBHist tail)

private theorem ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanCompletionFields : ArchimedeanCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanCompletionUp.mk F K R D O E H C P N =>
      [F, K, R, D, O, E, H, C, P, N]

def archimedeanCompletionToEventFlow : ArchimedeanCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (archimedeanCompletionFields x).map archimedeanCompletionEncodeBHist

private def archimedeanCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => archimedeanCompletionEventAt index rest

def archimedeanCompletionFromEventFlow (ef : EventFlow) :
    Option ArchimedeanCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArchimedeanCompletionUp.mk
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 0 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 1 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 2 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 3 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 4 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 5 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 6 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 7 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 8 ef))
      (archimedeanCompletionDecodeBHist (archimedeanCompletionEventAt 9 ef)))

private theorem ArchimedeanCompletionTasteGate_single_carrier_alignment_round_trip
    (x : ArchimedeanCompletionUp) :
    archimedeanCompletionFromEventFlow (archimedeanCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F K R D O E H C P N =>
      change
        some
          (ArchimedeanCompletionUp.mk
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist F))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist K))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist R))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist D))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist O))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist E))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist H))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist C))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist P))
            (archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist N))) =
          some (ArchimedeanCompletionUp.mk F K R D O E H C P N)
      rw [ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode F,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode K,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode R,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode D,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode O,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode E,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode H,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode C,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode P,
        ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArchimedeanCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArchimedeanCompletionUp} :
    archimedeanCompletionToEventFlow x = archimedeanCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanCompletionFromEventFlow (archimedeanCompletionToEventFlow x) =
        archimedeanCompletionFromEventFlow (archimedeanCompletionToEventFlow y) :=
    congrArg archimedeanCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArchimedeanCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArchimedeanCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ArchimedeanCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ArchimedeanCompletionUp,
      archimedeanCompletionFields x = archimedeanCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ K₁ R₁ D₁ O₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ K₂ R₂ D₂ O₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance archimedeanCompletionBHistCarrier :
    BHistCarrier ArchimedeanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanCompletionToEventFlow
  fromEventFlow := archimedeanCompletionFromEventFlow

instance archimedeanCompletionChapterTasteGate :
    ChapterTasteGate ArchimedeanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanCompletionFromEventFlow
      (archimedeanCompletionToEventFlow x) = some x
    exact ArchimedeanCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArchimedeanCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance archimedeanCompletionFieldFaithful :
    FieldFaithful ArchimedeanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanCompletionFields
  field_faithful := ArchimedeanCompletionTasteGate_single_carrier_alignment_fields_faithful

instance archimedeanCompletionNontrivial : Nontrivial ArchimedeanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArchimedeanCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArchimedeanCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ArchimedeanCompletionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ArchimedeanCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanCompletionChapterTasteGate

theorem ArchimedeanCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      archimedeanCompletionDecodeBHist (archimedeanCompletionEncodeBHist h) = h) ∧
      (∀ x : ArchimedeanCompletionUp,
        archimedeanCompletionFromEventFlow (archimedeanCompletionToEventFlow x) =
          some x) ∧
      (∀ x y : ArchimedeanCompletionUp,
        archimedeanCompletionToEventFlow x = archimedeanCompletionToEventFlow y →
          x = y) ∧
      archimedeanCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ArchimedeanCompletionTasteGate_single_carrier_alignment_decode_encode,
      ArchimedeanCompletionTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        ArchimedeanCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ArchimedeanCompletionUp
