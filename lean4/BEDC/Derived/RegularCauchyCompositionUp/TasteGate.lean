import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompositionUp : Type where
  | mk (S T W D K E H C P N : BHist) : RegularCauchyCompositionUp
  deriving DecidableEq

def regularCauchyCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompositionEncodeBHist h

def regularCauchyCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompositionDecodeBHist tail)

private theorem RegularCauchyCompositionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompositionFields : RegularCauchyCompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompositionUp.mk S T W D K E H C P N => [S, T, W, D, K, E, H, C, P, N]

def regularCauchyCompositionToEventFlow : RegularCauchyCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regularCauchyCompositionEncodeBHist (regularCauchyCompositionFields x)

private def regularCauchyCompositionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompositionRawAt index rest

def regularCauchyCompositionFromEventFlow
    (flow : EventFlow) : Option RegularCauchyCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompositionUp.mk
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 0 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 1 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 2 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 3 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 4 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 5 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 6 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 7 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 8 flow))
      (regularCauchyCompositionDecodeBHist (regularCauchyCompositionRawAt 9 flow)))

private theorem RegularCauchyCompositionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompositionUp,
      regularCauchyCompositionFromEventFlow (regularCauchyCompositionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W D K E H C P N =>
      change
        some
          (RegularCauchyCompositionUp.mk
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist S))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist T))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist W))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist D))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist K))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist E))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist H))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist C))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist P))
            (regularCauchyCompositionDecodeBHist (regularCauchyCompositionEncodeBHist N))) =
          some (RegularCauchyCompositionUp.mk S T W D K E H C P N)
      rw [RegularCauchyCompositionTasteGate_single_carrier_alignment_decode S,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode T,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode W,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode D,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode K,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode E,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCompositionTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyCompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompositionUp} :
    regularCauchyCompositionToEventFlow x = regularCauchyCompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompositionFromEventFlow (regularCauchyCompositionToEventFlow x) =
        regularCauchyCompositionFromEventFlow (regularCauchyCompositionToEventFlow y) :=
    congrArg regularCauchyCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyCompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyCompositionTasteGate_single_carrier_alignment_round_trip y)))

private theorem regularCauchyComposition_field_faithful :
    ∀ x y : RegularCauchyCompositionUp,
      regularCauchyCompositionFields x = regularCauchyCompositionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance regularCauchyCompositionBHistCarrier : BHistCarrier RegularCauchyCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompositionToEventFlow
  fromEventFlow := regularCauchyCompositionFromEventFlow

instance regularCauchyCompositionChapterTasteGate :
    ChapterTasteGate RegularCauchyCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyCompositionFromEventFlow (regularCauchyCompositionToEventFlow x) = some x
    exact RegularCauchyCompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyCompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyCompositionFieldFaithful :
    FieldFaithful RegularCauchyCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompositionFields
  field_faithful := regularCauchyComposition_field_faithful

instance regularCauchyCompositionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompositionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCompositionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompositionChapterTasteGate

theorem RegularCauchyCompositionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyCompositionUp) ∧
      Nonempty (FieldFaithful RegularCauchyCompositionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyCompositionUp) ∧
          (∀ h : BHist,
            regularCauchyCompositionDecodeBHist
              (regularCauchyCompositionEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyCompositionUp,
              regularCauchyCompositionFromEventFlow
                (regularCauchyCompositionToEventFlow x) = some x) ∧
              (∀ x y : RegularCauchyCompositionUp,
                regularCauchyCompositionToEventFlow x =
                    regularCauchyCompositionToEventFlow y →
                  x = y) ∧
                regularCauchyCompositionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyCompositionChapterTasteGate⟩,
      ⟨regularCauchyCompositionFieldFaithful⟩,
      ⟨regularCauchyCompositionNontrivial⟩,
      RegularCauchyCompositionTasteGate_single_carrier_alignment_decode,
      RegularCauchyCompositionTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact RegularCauchyCompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyCompositionUp
