import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwartzSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwartzSpaceUp : Type where
  | mk (F V I G D R T H C P N : BHist) : SchwartzSpaceUp
  deriving DecidableEq

def schwartzSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwartzSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwartzSpaceEncodeBHist h

def schwartzSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwartzSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwartzSpaceDecodeBHist tail)

private theorem schwartzSpaceDecode_encode_bhist :
    ∀ h : BHist, schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwartzSpaceToEventFlow : SchwartzSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SchwartzSpaceUp.mk F V I G D R T H C P N =>
      [schwartzSpaceEncodeBHist F,
        schwartzSpaceEncodeBHist V,
        schwartzSpaceEncodeBHist I,
        schwartzSpaceEncodeBHist G,
        schwartzSpaceEncodeBHist D,
        schwartzSpaceEncodeBHist R,
        schwartzSpaceEncodeBHist T,
        schwartzSpaceEncodeBHist H,
        schwartzSpaceEncodeBHist C,
        schwartzSpaceEncodeBHist P,
        schwartzSpaceEncodeBHist N]

private def schwartzSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schwartzSpaceEventAtDefault index rest

def schwartzSpaceFromEventFlow (ef : EventFlow) : Option SchwartzSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SchwartzSpaceUp.mk
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 0 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 1 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 2 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 3 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 4 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 5 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 6 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 7 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 8 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 9 ef))
      (schwartzSpaceDecodeBHist (schwartzSpaceEventAtDefault 10 ef)))

private theorem schwartzSpace_round_trip :
    ∀ x : SchwartzSpaceUp,
      schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F V I G D R T H C P N =>
      change
        some
          (SchwartzSpaceUp.mk
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist F))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist V))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist I))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist G))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist D))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist R))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist T))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist H))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist C))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist P))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist N))) =
          some (SchwartzSpaceUp.mk F V I G D R T H C P N)
      rw [schwartzSpaceDecode_encode_bhist F,
        schwartzSpaceDecode_encode_bhist V,
        schwartzSpaceDecode_encode_bhist I,
        schwartzSpaceDecode_encode_bhist G,
        schwartzSpaceDecode_encode_bhist D,
        schwartzSpaceDecode_encode_bhist R,
        schwartzSpaceDecode_encode_bhist T,
        schwartzSpaceDecode_encode_bhist H,
        schwartzSpaceDecode_encode_bhist C,
        schwartzSpaceDecode_encode_bhist P,
        schwartzSpaceDecode_encode_bhist N]

private theorem schwartzSpaceToEventFlow_injective {x y : SchwartzSpaceUp} :
    schwartzSpaceToEventFlow x = schwartzSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) =
        schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow y) :=
    congrArg schwartzSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schwartzSpace_round_trip x).symm
      (Eq.trans hread (schwartzSpace_round_trip y)))

private def schwartzSpaceFields : SchwartzSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwartzSpaceUp.mk F V I G D R T H C P N => [F, V, I, G, D, R, T, H, C, P, N]

private theorem schwartzSpace_field_faithful :
    ∀ x y : SchwartzSpaceUp, schwartzSpaceFields x = schwartzSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ V₁ I₁ G₁ D₁ R₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ V₂ I₂ G₂ D₂ R₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance schwartzSpaceBHistCarrier : BHistCarrier SchwartzSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwartzSpaceToEventFlow
  fromEventFlow := schwartzSpaceFromEventFlow

instance schwartzSpaceChapterTasteGate : ChapterTasteGate SchwartzSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) = some x
    exact schwartzSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schwartzSpaceToEventFlow_injective heq)

instance schwartzSpaceFieldFaithful : FieldFaithful SchwartzSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := schwartzSpaceFields
  field_faithful := schwartzSpace_field_faithful

instance schwartzSpaceNontrivial : Nontrivial SchwartzSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SchwartzSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SchwartzSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SchwartzSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schwartzSpaceChapterTasteGate

theorem SchwartzSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist h) = h) ∧
      (∀ x : SchwartzSpaceUp,
        schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) = some x) ∧
        (∀ x y : SchwartzSpaceUp,
          schwartzSpaceToEventFlow x = schwartzSpaceToEventFlow y → x = y) ∧
          schwartzSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact schwartzSpaceDecode_encode_bhist
  · constructor
    · exact schwartzSpace_round_trip
    · constructor
      · intro x y heq
        exact schwartzSpaceToEventFlow_injective heq
      · rfl

end BEDC.Derived.SchwartzSpaceUp.TasteGate
