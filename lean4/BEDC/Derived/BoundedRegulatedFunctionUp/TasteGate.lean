import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRegulatedFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRegulatedFunctionUp : Type where
  | mk (F B E H C P N : BHist) : BoundedRegulatedFunctionUp
  deriving DecidableEq

def boundedRegulatedFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRegulatedFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRegulatedFunctionEncodeBHist h

def boundedRegulatedFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRegulatedFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRegulatedFunctionDecodeBHist tail)

private theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRegulatedFunctionFields : BoundedRegulatedFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRegulatedFunctionUp.mk F B E H C P N => [F, B, E, H, C, P, N]

def boundedRegulatedFunctionToEventFlow : BoundedRegulatedFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedRegulatedFunctionFields x).map boundedRegulatedFunctionEncodeBHist

private def boundedRegulatedFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedRegulatedFunctionEventAtDefault index rest

def boundedRegulatedFunctionFromEventFlow : EventFlow → Option BoundedRegulatedFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BoundedRegulatedFunctionUp.mk
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 0 ef))
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 1 ef))
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 2 ef))
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 3 ef))
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 4 ef))
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 5 ef))
        (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAtDefault 6 ef)))

private theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedRegulatedFunctionUp,
      boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B E H C P N =>
      change
        some
          (BoundedRegulatedFunctionUp.mk
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist F))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist B))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist E))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist H))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist C))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist P))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist N))) =
          some (BoundedRegulatedFunctionUp.mk F B E H C P N)
      rw [BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode F,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode B,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode E,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode H,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode C,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode P,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode N]

private theorem boundedRegulatedFunctionToEventFlow_injective
    {x y : BoundedRegulatedFunctionUp} :
    boundedRegulatedFunctionToEventFlow x = boundedRegulatedFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow x) =
        boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow y) :=
    congrArg boundedRegulatedFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem boundedRegulatedFunction_field_faithful :
    ∀ x y : BoundedRegulatedFunctionUp,
      boundedRegulatedFunctionFields x = boundedRegulatedFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ B₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ B₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundedRegulatedFunctionBHistCarrier :
    BHistCarrier BoundedRegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRegulatedFunctionToEventFlow
  fromEventFlow := boundedRegulatedFunctionFromEventFlow

instance boundedRegulatedFunctionChapterTasteGate :
    ChapterTasteGate BoundedRegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow x) = some x
    exact BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedRegulatedFunctionToEventFlow_injective heq)

instance boundedRegulatedFunctionFieldFaithful :
    FieldFaithful BoundedRegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedRegulatedFunctionFields
  field_faithful := boundedRegulatedFunction_field_faithful

instance boundedRegulatedFunctionNontrivial :
    Nontrivial BoundedRegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRegulatedFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BoundedRegulatedFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedRegulatedFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRegulatedFunctionChapterTasteGate

theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BoundedRegulatedFunctionUp) ∧
      Nonempty (ChapterTasteGate BoundedRegulatedFunctionUp) ∧
      Nonempty (FieldFaithful BoundedRegulatedFunctionUp) ∧
      Nonempty (Nontrivial BoundedRegulatedFunctionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨boundedRegulatedFunctionBHistCarrier⟩,
      ⟨⟨boundedRegulatedFunctionChapterTasteGate⟩,
        ⟨⟨boundedRegulatedFunctionFieldFaithful⟩, ⟨boundedRegulatedFunctionNontrivial⟩⟩⟩⟩

end BEDC.Derived.BoundedRegulatedFunctionUp
