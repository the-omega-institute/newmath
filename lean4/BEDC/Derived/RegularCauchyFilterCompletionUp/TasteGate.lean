import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterCompletionUp : Type where
  | mk (L F S D R E H C P N : BHist) : RegularCauchyFilterCompletionUp
  deriving DecidableEq

def regularCauchyFilterCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterCompletionEncodeBHist h

def regularCauchyFilterCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterCompletionDecodeBHist tail)

private theorem RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFilterCompletionFields :
    RegularCauchyFilterCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterCompletionUp.mk L F S D R E H C P N =>
      [L, F, S, D, R, E, H, C, P, N]

def regularCauchyFilterCompletionToEventFlow :
    RegularCauchyFilterCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyFilterCompletionFields x).map
        regularCauchyFilterCompletionEncodeBHist

private def regularCauchyFilterCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFilterCompletionEventAt index rest

def regularCauchyFilterCompletionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFilterCompletionUp.mk
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 0 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 1 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 2 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 3 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 4 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 5 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 6 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 7 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 8 ef))
      (regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEventAt 9 ef)))

private theorem RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyFilterCompletionUp) :
    regularCauchyFilterCompletionFromEventFlow
      (regularCauchyFilterCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L F S D R E H C P N =>
      change
        some
          (RegularCauchyFilterCompletionUp.mk
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist L))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist F))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist S))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist D))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist R))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist E))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist H))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist C))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist P))
            (regularCauchyFilterCompletionDecodeBHist
              (regularCauchyFilterCompletionEncodeBHist N))) =
          some (RegularCauchyFilterCompletionUp.mk L F S D R E H C P N)
      rw [RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode F,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFilterCompletionUp} :
    regularCauchyFilterCompletionToEventFlow x =
        regularCauchyFilterCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterCompletionFromEventFlow
          (regularCauchyFilterCompletionToEventFlow x) =
        regularCauchyFilterCompletionFromEventFlow
          (regularCauchyFilterCompletionToEventFlow y) :=
    congrArg regularCauchyFilterCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyFilterCompletionUp,
      regularCauchyFilterCompletionFields x =
        regularCauchyFilterCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ F₁ S₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ F₂ S₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyFilterCompletionBHistCarrier :
    BHistCarrier RegularCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterCompletionToEventFlow
  fromEventFlow := regularCauchyFilterCompletionFromEventFlow

instance regularCauchyFilterCompletionChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFilterCompletionFromEventFlow
        (regularCauchyFilterCompletionToEventFlow x) = some x
    exact RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyFilterCompletionFieldFaithful :
    FieldFaithful RegularCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyFilterCompletionFields
  field_faithful :=
    RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyFilterCompletionNontrivial :
    Nontrivial RegularCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyFilterCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyFilterCompletionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFilterCompletionChapterTasteGate

theorem RegularCauchyFilterCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyFilterCompletionDecodeBHist
        (regularCauchyFilterCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyFilterCompletionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyFilterCompletionUp) ∧
          regularCauchyFilterCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyFilterCompletionBHistCarrier⟩,
      ⟨regularCauchyFilterCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyFilterCompletionUp
