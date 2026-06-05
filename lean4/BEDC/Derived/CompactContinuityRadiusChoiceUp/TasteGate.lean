import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactContinuityRadiusChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactContinuityRadiusChoiceUp : Type where
  | mk (K F M Q D L U H C P N : BHist) : CompactContinuityRadiusChoiceUp
  deriving DecidableEq

def compactContinuityRadiusChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactContinuityRadiusChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactContinuityRadiusChoiceEncodeBHist h

def compactContinuityRadiusChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactContinuityRadiusChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactContinuityRadiusChoiceDecodeBHist tail)

private theorem compactContinuityRadiusChoiceDecodeEncodeBHist :
    ∀ h : BHist,
      compactContinuityRadiusChoiceDecodeBHist
          (compactContinuityRadiusChoiceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactContinuityRadiusChoiceFields :
    CompactContinuityRadiusChoiceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactContinuityRadiusChoiceUp.mk K F M Q D L U H C P N =>
      [K, F, M, Q, D, L, U, H, C, P, N]

def compactContinuityRadiusChoiceToEventFlow :
    CompactContinuityRadiusChoiceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactContinuityRadiusChoiceFields x).map
    compactContinuityRadiusChoiceEncodeBHist

private def compactContinuityRadiusChoiceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactContinuityRadiusChoiceEventAtDefault index rest

def compactContinuityRadiusChoiceFromEventFlow
    (ef : EventFlow) : Option CompactContinuityRadiusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactContinuityRadiusChoiceUp.mk
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 0 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 1 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 2 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 3 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 4 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 5 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 6 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 7 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 8 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 9 ef))
      (compactContinuityRadiusChoiceDecodeBHist
        (compactContinuityRadiusChoiceEventAtDefault 10 ef)))

private theorem compactContinuityRadiusChoiceRoundTrip :
    ∀ x : CompactContinuityRadiusChoiceUp,
      compactContinuityRadiusChoiceFromEventFlow
          (compactContinuityRadiusChoiceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M Q D L U H C P N =>
      change
        some
          (CompactContinuityRadiusChoiceUp.mk
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist K))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist F))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist M))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist Q))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist D))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist L))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist U))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist H))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist C))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist P))
            (compactContinuityRadiusChoiceDecodeBHist
              (compactContinuityRadiusChoiceEncodeBHist N))) =
          some (CompactContinuityRadiusChoiceUp.mk K F M Q D L U H C P N)
      rw [compactContinuityRadiusChoiceDecodeEncodeBHist K,
        compactContinuityRadiusChoiceDecodeEncodeBHist F,
        compactContinuityRadiusChoiceDecodeEncodeBHist M,
        compactContinuityRadiusChoiceDecodeEncodeBHist Q,
        compactContinuityRadiusChoiceDecodeEncodeBHist D,
        compactContinuityRadiusChoiceDecodeEncodeBHist L,
        compactContinuityRadiusChoiceDecodeEncodeBHist U,
        compactContinuityRadiusChoiceDecodeEncodeBHist H,
        compactContinuityRadiusChoiceDecodeEncodeBHist C,
        compactContinuityRadiusChoiceDecodeEncodeBHist P,
        compactContinuityRadiusChoiceDecodeEncodeBHist N]

private theorem compactContinuityRadiusChoiceToEventFlow_injective
    {x y : CompactContinuityRadiusChoiceUp} :
    compactContinuityRadiusChoiceToEventFlow x =
        compactContinuityRadiusChoiceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactContinuityRadiusChoiceFromEventFlow
          (compactContinuityRadiusChoiceToEventFlow x) =
        compactContinuityRadiusChoiceFromEventFlow
          (compactContinuityRadiusChoiceToEventFlow y) :=
    congrArg compactContinuityRadiusChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactContinuityRadiusChoiceRoundTrip x).symm
      (Eq.trans hread (compactContinuityRadiusChoiceRoundTrip y)))

private theorem compactContinuityRadiusChoiceFields_faithful :
    ∀ x y : CompactContinuityRadiusChoiceUp,
      compactContinuityRadiusChoiceFields x = compactContinuityRadiusChoiceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ M₁ Q₁ D₁ L₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ M₂ Q₂ D₂ L₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactContinuityRadiusChoiceBHistCarrier :
    BHistCarrier CompactContinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactContinuityRadiusChoiceToEventFlow
  fromEventFlow := compactContinuityRadiusChoiceFromEventFlow

instance compactContinuityRadiusChoiceChapterTasteGate :
    ChapterTasteGate CompactContinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactContinuityRadiusChoiceFromEventFlow
          (compactContinuityRadiusChoiceToEventFlow x) =
        some x
    exact compactContinuityRadiusChoiceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactContinuityRadiusChoiceToEventFlow_injective heq)

instance compactContinuityRadiusChoiceFieldFaithful :
    FieldFaithful CompactContinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactContinuityRadiusChoiceFields
  field_faithful := compactContinuityRadiusChoiceFields_faithful

instance compactContinuityRadiusChoiceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactContinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactContinuityRadiusChoiceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactContinuityRadiusChoiceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactContinuityRadiusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactContinuityRadiusChoiceChapterTasteGate

theorem CompactContinuityRadiusChoiceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactContinuityRadiusChoiceDecodeBHist
          (compactContinuityRadiusChoiceEncodeBHist h) =
        h) ∧
      (∀ x : CompactContinuityRadiusChoiceUp,
        compactContinuityRadiusChoiceFromEventFlow
            (compactContinuityRadiusChoiceToEventFlow x) =
          some x) ∧
        (∀ x y : CompactContinuityRadiusChoiceUp,
          compactContinuityRadiusChoiceToEventFlow x =
              compactContinuityRadiusChoiceToEventFlow y ->
            x = y) ∧
          compactContinuityRadiusChoiceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨compactContinuityRadiusChoiceDecodeEncodeBHist,
      compactContinuityRadiusChoiceRoundTrip,
      (fun _ _ heq => compactContinuityRadiusChoiceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactContinuityRadiusChoiceUp
