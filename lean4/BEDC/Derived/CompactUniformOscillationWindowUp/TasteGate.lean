import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformOscillationWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformOscillationWindowUp : Type where
  | mk (K F U O M B W R D S H C P N : BHist) : CompactUniformOscillationWindowUp
  deriving DecidableEq

def compactUniformOscillationWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformOscillationWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformOscillationWindowEncodeBHist h

def compactUniformOscillationWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformOscillationWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformOscillationWindowDecodeBHist tail)

private theorem compactUniformOscillationWindow_decode_encode_bhist :
    ∀ h : BHist,
      compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformOscillationWindowFields :
    CompactUniformOscillationWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformOscillationWindowUp.mk K F U O M B W R D S H C P N =>
      [K, F, U, O, M, B, W, R, D, S, H, C, P, N]

def compactUniformOscillationWindowToEventFlow :
    CompactUniformOscillationWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformOscillationWindowUp.mk K F U O M B W R D S H C P N =>
      [[BMark.b0], compactUniformOscillationWindowEncodeBHist K,
        [BMark.b1, BMark.b0], compactUniformOscillationWindowEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0], compactUniformOscillationWindowEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0], compactUniformOscillationWindowEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0], compactUniformOscillationWindowEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0], compactUniformOscillationWindowEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          compactUniformOscillationWindowEncodeBHist N]

private def compactUniformOscillationWindowEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformOscillationWindowEventAtDefault index rest

def compactUniformOscillationWindowFromEventFlow
    (ef : EventFlow) : Option CompactUniformOscillationWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformOscillationWindowUp.mk
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 1 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 3 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 5 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 7 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 9 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 11 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 13 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 15 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 17 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 19 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 21 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 23 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 25 ef))
      (compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEventAtDefault 27 ef)))

private theorem compactUniformOscillationWindow_round_trip :
    ∀ x : CompactUniformOscillationWindowUp,
      compactUniformOscillationWindowFromEventFlow
        (compactUniformOscillationWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F U O M B W R D S H C P N =>
      change
        some
          (CompactUniformOscillationWindowUp.mk
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist K))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist F))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist U))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist O))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist M))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist B))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist W))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist R))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist D))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist S))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist H))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist C))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist P))
            (compactUniformOscillationWindowDecodeBHist
              (compactUniformOscillationWindowEncodeBHist N))) =
          some (CompactUniformOscillationWindowUp.mk K F U O M B W R D S H C P N)
      rw [compactUniformOscillationWindow_decode_encode_bhist K,
        compactUniformOscillationWindow_decode_encode_bhist F,
        compactUniformOscillationWindow_decode_encode_bhist U,
        compactUniformOscillationWindow_decode_encode_bhist O,
        compactUniformOscillationWindow_decode_encode_bhist M,
        compactUniformOscillationWindow_decode_encode_bhist B,
        compactUniformOscillationWindow_decode_encode_bhist W,
        compactUniformOscillationWindow_decode_encode_bhist R,
        compactUniformOscillationWindow_decode_encode_bhist D,
        compactUniformOscillationWindow_decode_encode_bhist S,
        compactUniformOscillationWindow_decode_encode_bhist H,
        compactUniformOscillationWindow_decode_encode_bhist C,
        compactUniformOscillationWindow_decode_encode_bhist P,
        compactUniformOscillationWindow_decode_encode_bhist N]

private theorem compactUniformOscillationWindowToEventFlow_injective
    {x y : CompactUniformOscillationWindowUp} :
    compactUniformOscillationWindowToEventFlow x =
      compactUniformOscillationWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformOscillationWindowFromEventFlow
          (compactUniformOscillationWindowToEventFlow x) =
        compactUniformOscillationWindowFromEventFlow
          (compactUniformOscillationWindowToEventFlow y) :=
    congrArg compactUniformOscillationWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformOscillationWindow_round_trip x).symm
      (Eq.trans hread (compactUniformOscillationWindow_round_trip y)))

private theorem compactUniformOscillationWindow_fields_faithful :
    ∀ x y : CompactUniformOscillationWindowUp,
      compactUniformOscillationWindowFields x =
        compactUniformOscillationWindowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ U₁ O₁ M₁ B₁ W₁ R₁ D₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ U₂ O₂ M₂ B₂ W₂ R₂ D₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactUniformOscillationWindowBHistCarrier :
    BHistCarrier CompactUniformOscillationWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformOscillationWindowToEventFlow
  fromEventFlow := compactUniformOscillationWindowFromEventFlow

instance compactUniformOscillationWindowChapterTasteGate :
    ChapterTasteGate CompactUniformOscillationWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformOscillationWindowFromEventFlow
        (compactUniformOscillationWindowToEventFlow x) = some x
    exact compactUniformOscillationWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformOscillationWindowToEventFlow_injective heq)

instance compactUniformOscillationWindowFieldFaithful :
    FieldFaithful CompactUniformOscillationWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformOscillationWindowFields
  field_faithful := compactUniformOscillationWindow_fields_faithful

def taste_gate : ChapterTasteGate CompactUniformOscillationWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformOscillationWindowChapterTasteGate

instance compactUniformOscillationWindowNontrivial :
    Nontrivial CompactUniformOscillationWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformOscillationWindowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformOscillationWindowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactUniformOscillationWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformOscillationWindowDecodeBHist
        (compactUniformOscillationWindowEncodeBHist h) = h) ∧
      (∀ x : CompactUniformOscillationWindowUp,
        compactUniformOscillationWindowFromEventFlow
          (compactUniformOscillationWindowToEventFlow x) = some x) ∧
        (∀ x y : CompactUniformOscillationWindowUp,
          compactUniformOscillationWindowToEventFlow x =
            compactUniformOscillationWindowToEventFlow y → x = y) ∧
          compactUniformOscillationWindowEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨compactUniformOscillationWindow_decode_encode_bhist,
      compactUniformOscillationWindow_round_trip,
      (fun _ _ heq => compactUniformOscillationWindowToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactUniformOscillationWindowUp
