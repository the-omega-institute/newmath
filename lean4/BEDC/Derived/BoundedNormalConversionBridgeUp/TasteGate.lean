import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedNormalConversionBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedNormalConversionBridgeUp : Type where
  | mk (D F O E S R H C P N : BHist) : BoundedNormalConversionBridgeUp
  deriving DecidableEq

def boundedNormalConversionBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedNormalConversionBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedNormalConversionBridgeEncodeBHist h

def boundedNormalConversionBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedNormalConversionBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedNormalConversionBridgeDecodeBHist tail)

private theorem BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedNormalConversionBridgeDecodeBHist
        (boundedNormalConversionBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedNormalConversionBridgeFields : BoundedNormalConversionBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedNormalConversionBridgeUp.mk D F O E S R H C P N => [D, F, O, E, S, R, H, C, P, N]

def boundedNormalConversionBridgeToEventFlow : BoundedNormalConversionBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedNormalConversionBridgeFields x).map boundedNormalConversionBridgeEncodeBHist

private def boundedNormalConversionBridgeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedNormalConversionBridgeEventAt index rest

def boundedNormalConversionBridgeFromEventFlow :
    EventFlow → Option BoundedNormalConversionBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BoundedNormalConversionBridgeUp.mk
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 0 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 1 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 2 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 3 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 4 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 5 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 6 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 7 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 8 ef))
          (boundedNormalConversionBridgeDecodeBHist (boundedNormalConversionBridgeEventAt 9 ef)))

private theorem BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedNormalConversionBridgeUp,
      boundedNormalConversionBridgeFromEventFlow
          (boundedNormalConversionBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D F O E S R H C P N =>
      change
        some
          (BoundedNormalConversionBridgeUp.mk
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist D))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist F))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist O))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist E))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist S))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist R))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist H))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist C))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist P))
            (boundedNormalConversionBridgeDecodeBHist
              (boundedNormalConversionBridgeEncodeBHist N))) =
          some (BoundedNormalConversionBridgeUp.mk D F O E S R H C P N)
      rw [BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode D,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode F,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode O,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode E,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode S,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode R,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode H,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode C,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode P,
        BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedNormalConversionBridgeUp} :
    boundedNormalConversionBridgeToEventFlow x = boundedNormalConversionBridgeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedNormalConversionBridgeFromEventFlow (boundedNormalConversionBridgeToEventFlow x) =
        boundedNormalConversionBridgeFromEventFlow (boundedNormalConversionBridgeToEventFlow y) :=
    congrArg boundedNormalConversionBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BoundedNormalConversionBridgeUp,
      boundedNormalConversionBridgeFields x = boundedNormalConversionBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D₁ F₁ O₁ E₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ F₂ O₂ E₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance boundedNormalConversionBridgeBHistCarrier :
    BHistCarrier BoundedNormalConversionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedNormalConversionBridgeToEventFlow
  fromEventFlow := boundedNormalConversionBridgeFromEventFlow

instance boundedNormalConversionBridgeChapterTasteGate :
    ChapterTasteGate BoundedNormalConversionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedNormalConversionBridgeFromEventFlow (boundedNormalConversionBridgeToEventFlow x) =
        some x
    exact BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedNormalConversionBridgeFieldFaithful :
    FieldFaithful BoundedNormalConversionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedNormalConversionBridgeFields
  field_faithful :=
    BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_field_faithful

instance boundedNormalConversionBridgeNontrivial : Nontrivial BoundedNormalConversionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedNormalConversionBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedNormalConversionBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedNormalConversionBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedNormalConversionBridgeDecodeBHist
      (boundedNormalConversionBridgeEncodeBHist h) = h) ∧
      (∀ x : BoundedNormalConversionBridgeUp,
        boundedNormalConversionBridgeFromEventFlow
            (boundedNormalConversionBridgeToEventFlow x) =
          some x) ∧
        (∀ x y : BoundedNormalConversionBridgeUp,
          boundedNormalConversionBridgeToEventFlow x =
              boundedNormalConversionBridgeToEventFlow y →
            x = y) ∧
          boundedNormalConversionBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          BoundedNormalConversionBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.BoundedNormalConversionBridgeUp
