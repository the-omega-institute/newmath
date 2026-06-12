import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterComparisonUp : Type where
  | mk (F B T S D R H C P N : BHist) : RegularCauchyFilterComparisonUp
  deriving DecidableEq

def regularCauchyFilterComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterComparisonEncodeBHist h

def regularCauchyFilterComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterComparisonDecodeBHist tail)

private theorem RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFilterComparisonFields :
    RegularCauchyFilterComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterComparisonUp.mk F B T S D R H C P N =>
      [F, B, T, S, D, R, H, C, P, N]

def regularCauchyFilterComparisonToEventFlow :
    RegularCauchyFilterComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyFilterComparisonFields x).map
        regularCauchyFilterComparisonEncodeBHist

private def regularCauchyFilterComparisonEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyFilterComparisonEventAtDefault index rest

def regularCauchyFilterComparisonFromEventFlow
    (ef : EventFlow) : Option RegularCauchyFilterComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFilterComparisonUp.mk
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 0 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 1 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 2 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 3 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 4 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 5 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 6 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 7 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 8 ef))
      (regularCauchyFilterComparisonDecodeBHist
        (regularCauchyFilterComparisonEventAtDefault 9 ef)))

private theorem RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyFilterComparisonUp,
      regularCauchyFilterComparisonFromEventFlow
          (regularCauchyFilterComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B T S D R H C P N =>
      change
        some
            (RegularCauchyFilterComparisonUp.mk
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist F))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist B))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist T))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist S))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist D))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist R))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist H))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist C))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist P))
              (regularCauchyFilterComparisonDecodeBHist
                (regularCauchyFilterComparisonEncodeBHist N))) =
          some (RegularCauchyFilterComparisonUp.mk F B T S D R H C P N)
      rw [RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode F,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFilterComparisonUp} :
    regularCauchyFilterComparisonToEventFlow x =
        regularCauchyFilterComparisonToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterComparisonFromEventFlow
          (regularCauchyFilterComparisonToEventFlow x) =
        regularCauchyFilterComparisonFromEventFlow
          (regularCauchyFilterComparisonToEventFlow y) :=
    congrArg regularCauchyFilterComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyFilterComparisonUp,
      regularCauchyFilterComparisonFields x =
          regularCauchyFilterComparisonFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ B₁ T₁ S₁ D₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ B₂ T₂ S₂ D₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyFilterComparisonBHistCarrier :
    BHistCarrier RegularCauchyFilterComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterComparisonToEventFlow
  fromEventFlow := regularCauchyFilterComparisonFromEventFlow

instance regularCauchyFilterComparisonChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFilterComparisonFromEventFlow
          (regularCauchyFilterComparisonToEventFlow x) = some x
    exact RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyFilterComparisonFieldFaithful :
    FieldFaithful RegularCauchyFilterComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyFilterComparisonFields
  field_faithful :=
    RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyFilterComparisonNontrivial :
    Nontrivial RegularCauchyFilterComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyFilterComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyFilterComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyFilterComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFilterComparisonChapterTasteGate

theorem RegularCauchyFilterComparisonTasteGate_single_carrier_alignment :
    regularCauchyFilterComparisonEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      regularCauchyFilterComparisonEncodeBHist (BHist.e0 BHist.Empty) =
        [BMark.b0] ∧
        (∀ h : BHist,
          regularCauchyFilterComparisonDecodeBHist
            (regularCauchyFilterComparisonEncodeBHist h) = h) ∧
          (∀ x : RegularCauchyFilterComparisonUp,
            regularCauchyFilterComparisonFromEventFlow
              (regularCauchyFilterComparisonToEventFlow x) = some x) ∧
            (∀ x y : RegularCauchyFilterComparisonUp,
              regularCauchyFilterComparisonToEventFlow x =
                  regularCauchyFilterComparisonToEventFlow y →
                x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨rfl, rfl,
      RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RegularCauchyFilterComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
          heq⟩

end BEDC.Derived.RegularCauchyFilterComparisonUp
