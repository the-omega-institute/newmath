import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactFilterDiniMonotoneUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactFilterDiniMonotoneUp : Type where
  | mk (K F epsilon rho M T R P N : BHist) : CompactFilterDiniMonotoneUp
  deriving DecidableEq

def compactFilterDiniMonotoneEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactFilterDiniMonotoneEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactFilterDiniMonotoneEncodeBHist h

def compactFilterDiniMonotoneDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactFilterDiniMonotoneDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactFilterDiniMonotoneDecodeBHist tail)

private theorem CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactFilterDiniMonotoneDecodeBHist
          (compactFilterDiniMonotoneEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactFilterDiniMonotoneFields : CompactFilterDiniMonotoneUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactFilterDiniMonotoneUp.mk K F epsilon rho M T R P N =>
      [K, F, epsilon, rho, M, T, R, P, N]

def compactFilterDiniMonotoneToEventFlow :
    CompactFilterDiniMonotoneUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactFilterDiniMonotoneFields x).map compactFilterDiniMonotoneEncodeBHist

private def CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt index rest

def compactFilterDiniMonotoneFromEventFlow (ef : EventFlow) :
    Option CompactFilterDiniMonotoneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactFilterDiniMonotoneUp.mk
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 0 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 1 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 2 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 3 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 4 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 5 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 6 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 7 ef))
      (compactFilterDiniMonotoneDecodeBHist
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactFilterDiniMonotoneUp,
      compactFilterDiniMonotoneFromEventFlow (compactFilterDiniMonotoneToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F epsilon rho M T R P N =>
      change
        some
          (CompactFilterDiniMonotoneUp.mk
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist K))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist F))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist epsilon))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist rho))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist M))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist T))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist R))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist P))
            (compactFilterDiniMonotoneDecodeBHist
              (compactFilterDiniMonotoneEncodeBHist N))) =
          some (CompactFilterDiniMonotoneUp.mk K F epsilon rho M T R P N)
      rw [CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode K,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode F,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode epsilon,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode rho,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode M,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode T,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode R,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode P,
        CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactFilterDiniMonotoneUp} :
    compactFilterDiniMonotoneToEventFlow x = compactFilterDiniMonotoneToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactFilterDiniMonotoneFromEventFlow (compactFilterDiniMonotoneToEventFlow x) =
        compactFilterDiniMonotoneFromEventFlow (compactFilterDiniMonotoneToEventFlow y) :=
    congrArg compactFilterDiniMonotoneFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompactFilterDiniMonotoneUp,
      compactFilterDiniMonotoneFields x = compactFilterDiniMonotoneFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ epsilon₁ rho₁ M₁ T₁ R₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ epsilon₂ rho₂ M₂ T₂ R₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactFilterDiniMonotoneBHistCarrier :
    BHistCarrier CompactFilterDiniMonotoneUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactFilterDiniMonotoneToEventFlow
  fromEventFlow := compactFilterDiniMonotoneFromEventFlow

instance compactFilterDiniMonotoneChapterTasteGate :
    ChapterTasteGate CompactFilterDiniMonotoneUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactFilterDiniMonotoneFromEventFlow
        (compactFilterDiniMonotoneToEventFlow x) = some x
    exact CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactFilterDiniMonotoneFieldFaithful :
    FieldFaithful CompactFilterDiniMonotoneUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactFilterDiniMonotoneFields
  field_faithful :=
    CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_fields_faithful

instance compactFilterDiniMonotoneNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactFilterDiniMonotoneUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactFilterDiniMonotoneUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactFilterDiniMonotoneUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactFilterDiniMonotoneTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactFilterDiniMonotoneUp) ∧
      Nonempty (FieldFaithful CompactFilterDiniMonotoneUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactFilterDiniMonotoneUp) ∧
      (∀ h : BHist,
        compactFilterDiniMonotoneDecodeBHist
            (compactFilterDiniMonotoneEncodeBHist h) = h) ∧
      (∀ x : CompactFilterDiniMonotoneUp,
        compactFilterDiniMonotoneFromEventFlow
            (compactFilterDiniMonotoneToEventFlow x) = some x) ∧
      (∀ x y : CompactFilterDiniMonotoneUp,
        compactFilterDiniMonotoneToEventFlow x =
            compactFilterDiniMonotoneToEventFlow y →
          x = y) ∧
      compactFilterDiniMonotoneEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact Nonempty.intro compactFilterDiniMonotoneChapterTasteGate
  · constructor
    · exact Nonempty.intro compactFilterDiniMonotoneFieldFaithful
    · constructor
      · exact Nonempty.intro compactFilterDiniMonotoneNontrivial
      · constructor
        · exact CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                CompactFilterDiniMonotoneTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.CompactFilterDiniMonotoneUp
