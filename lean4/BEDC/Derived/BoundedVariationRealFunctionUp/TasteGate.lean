import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedVariationRealFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedVariationRealFunctionUp : Type where
  | mk (I F W R D B J H C P N : BHist) : BoundedVariationRealFunctionUp
  deriving DecidableEq

def boundedVariationRealFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedVariationRealFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedVariationRealFunctionEncodeBHist h

def boundedVariationRealFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedVariationRealFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedVariationRealFunctionDecodeBHist tail)

private theorem BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedVariationRealFunctionFields : BoundedVariationRealFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedVariationRealFunctionUp.mk I F W R D B J H C P N => [I, F, W, R, D, B, J, H, C, P, N]

def boundedVariationRealFunctionToEventFlow : BoundedVariationRealFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedVariationRealFunctionFields x).map boundedVariationRealFunctionEncodeBHist

private def boundedVariationRealFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedVariationRealFunctionEventAt index rest

def boundedVariationRealFunctionFromEventFlow
    (ef : EventFlow) : Option BoundedVariationRealFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedVariationRealFunctionUp.mk
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 0 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 1 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 2 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 3 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 4 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 5 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 6 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 7 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 8 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 9 ef))
      (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEventAt 10 ef)))

private theorem BoundedVariationRealFunctionTasteGate_single_carrier_alignment_round_trip
    (x : BoundedVariationRealFunctionUp) :
    boundedVariationRealFunctionFromEventFlow (boundedVariationRealFunctionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F W R D B J H C P N =>
      change
        some
          (BoundedVariationRealFunctionUp.mk
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist I))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist F))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist W))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist R))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist D))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist B))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist J))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist H))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist C))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist P))
            (boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist N))) =
          some (BoundedVariationRealFunctionUp.mk I F W R D B J H C P N)
      rw [BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode I,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode F,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode W,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode R,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode D,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode B,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode J,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode H,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode C,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode P,
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedVariationRealFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedVariationRealFunctionUp} :
    boundedVariationRealFunctionToEventFlow x =
      boundedVariationRealFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedVariationRealFunctionFromEventFlow (boundedVariationRealFunctionToEventFlow x) =
        boundedVariationRealFunctionFromEventFlow (boundedVariationRealFunctionToEventFlow y) :=
    congrArg boundedVariationRealFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedVariationRealFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedVariationRealFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedVariationRealFunctionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BoundedVariationRealFunctionUp,
      boundedVariationRealFunctionFields x = boundedVariationRealFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ W₁ R₁ D₁ B₁ J₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ F₂ W₂ R₂ D₂ B₂ J₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundedVariationRealFunctionBHistCarrier :
    BHistCarrier BoundedVariationRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedVariationRealFunctionToEventFlow
  fromEventFlow := boundedVariationRealFunctionFromEventFlow

instance boundedVariationRealFunctionChapterTasteGate :
    ChapterTasteGate BoundedVariationRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedVariationRealFunctionFromEventFlow
      (boundedVariationRealFunctionToEventFlow x) = some x
    exact BoundedVariationRealFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundedVariationRealFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedVariationRealFunctionFieldFaithful :
    FieldFaithful BoundedVariationRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedVariationRealFunctionFields
  field_faithful := BoundedVariationRealFunctionTasteGate_single_carrier_alignment_fields_faithful

instance boundedVariationRealFunctionNontrivial :
    Nontrivial BoundedVariationRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedVariationRealFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedVariationRealFunctionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def BoundedVariationRealFunctionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BoundedVariationRealFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedVariationRealFunctionChapterTasteGate

theorem BoundedVariationRealFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedVariationRealFunctionDecodeBHist (boundedVariationRealFunctionEncodeBHist h) = h) ∧
      (∀ x : BoundedVariationRealFunctionUp,
        boundedVariationRealFunctionFromEventFlow (boundedVariationRealFunctionToEventFlow x) =
          some x) ∧
        (∀ x y : BoundedVariationRealFunctionUp,
          boundedVariationRealFunctionToEventFlow x =
              boundedVariationRealFunctionToEventFlow y →
            x = y) ∧
          boundedVariationRealFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BoundedVariationRealFunctionTasteGate_single_carrier_alignment_decode_encode,
      BoundedVariationRealFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedVariationRealFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedVariationRealFunctionUp.TasteGate
