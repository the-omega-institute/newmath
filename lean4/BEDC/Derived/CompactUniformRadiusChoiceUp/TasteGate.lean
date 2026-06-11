import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformRadiusChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformRadiusChoiceUp : Type where
  | mk
      (compactMetric pointwiseModulus positiveRadius finiteFold uniformOutput transport replay
        provenance localName : BHist) :
        CompactUniformRadiusChoiceUp
  deriving DecidableEq

def compactUniformRadiusChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformRadiusChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformRadiusChoiceEncodeBHist h

def compactUniformRadiusChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformRadiusChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformRadiusChoiceDecodeBHist tail)

private theorem CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformRadiusChoiceFields : CompactUniformRadiusChoiceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformRadiusChoiceUp.mk compactMetric pointwiseModulus positiveRadius finiteFold
      uniformOutput transport replay provenance localName =>
      [compactMetric, pointwiseModulus, positiveRadius, finiteFold, uniformOutput, transport,
        replay, provenance, localName]

def compactUniformRadiusChoiceToEventFlow :
    CompactUniformRadiusChoiceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformRadiusChoiceFields x).map compactUniformRadiusChoiceEncodeBHist

private def compactUniformRadiusChoiceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformRadiusChoiceEventAt index rest

def compactUniformRadiusChoiceFromEventFlow :
    EventFlow → Option CompactUniformRadiusChoiceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CompactUniformRadiusChoiceUp.mk
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 0 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 1 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 2 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 3 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 4 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 5 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 6 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 7 ef))
          (compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEventAt 8 ef)))

private theorem CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformRadiusChoiceUp,
      compactUniformRadiusChoiceFromEventFlow (compactUniformRadiusChoiceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactMetric pointwiseModulus positiveRadius finiteFold uniformOutput transport replay
      provenance localName =>
      change
        some
          (CompactUniformRadiusChoiceUp.mk
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist compactMetric))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist pointwiseModulus))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist positiveRadius))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist finiteFold))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist uniformOutput))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist transport))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist replay))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist provenance))
            (compactUniformRadiusChoiceDecodeBHist
              (compactUniformRadiusChoiceEncodeBHist localName))) =
          some
            (CompactUniformRadiusChoiceUp.mk compactMetric pointwiseModulus positiveRadius
              finiteFold uniformOutput transport replay provenance localName)
      rw [CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
          compactMetric,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
          pointwiseModulus,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
          positiveRadius,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode finiteFold,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
          uniformOutput,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode transport,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode replay,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode provenance,
        CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformRadiusChoiceUp} :
    compactUniformRadiusChoiceToEventFlow x = compactUniformRadiusChoiceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformRadiusChoiceFromEventFlow (compactUniformRadiusChoiceToEventFlow x) =
        compactUniformRadiusChoiceFromEventFlow (compactUniformRadiusChoiceToEventFlow y) :=
    congrArg compactUniformRadiusChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompactUniformRadiusChoiceUp,
      compactUniformRadiusChoiceFields x = compactUniformRadiusChoiceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk compactMetric₁ pointwiseModulus₁ positiveRadius₁ finiteFold₁ uniformOutput₁ transport₁
      replay₁ provenance₁ localName₁ =>
      cases y with
      | mk compactMetric₂ pointwiseModulus₂ positiveRadius₂ finiteFold₂ uniformOutput₂ transport₂
          replay₂ provenance₂ localName₂ =>
          injection hfields with hcompactMetric tail0
          injection tail0 with hpointwiseModulus tail1
          injection tail1 with hpositiveRadius tail2
          injection tail2 with hfiniteFold tail3
          injection tail3 with huniformOutput tail4
          injection tail4 with htransport tail5
          injection tail5 with hreplay tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hlocalName _
          subst hcompactMetric
          subst hpointwiseModulus
          subst hpositiveRadius
          subst hfiniteFold
          subst huniformOutput
          subst htransport
          subst hreplay
          subst hprovenance
          subst hlocalName
          rfl

instance compactUniformRadiusChoiceBHistCarrier :
    BHistCarrier CompactUniformRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformRadiusChoiceToEventFlow
  fromEventFlow := compactUniformRadiusChoiceFromEventFlow

instance compactUniformRadiusChoiceChapterTasteGate :
    ChapterTasteGate CompactUniformRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformRadiusChoiceFromEventFlow (compactUniformRadiusChoiceToEventFlow x) =
      some x
    exact CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactUniformRadiusChoiceFieldFaithful :
    FieldFaithful CompactUniformRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformRadiusChoiceFields
  field_faithful :=
    CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_fields_faithful

instance compactUniformRadiusChoiceNontrivial :
    Nontrivial CompactUniformRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformRadiusChoiceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformRadiusChoiceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactUniformRadiusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformRadiusChoiceChapterTasteGate

theorem CompactUniformRadiusChoiceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformRadiusChoiceDecodeBHist (compactUniformRadiusChoiceEncodeBHist h) = h) ∧
      (∀ x : CompactUniformRadiusChoiceUp,
        compactUniformRadiusChoiceFromEventFlow (compactUniformRadiusChoiceToEventFlow x) =
          some x) ∧
      (∀ x y : CompactUniformRadiusChoiceUp,
        compactUniformRadiusChoiceToEventFlow x = compactUniformRadiusChoiceToEventFlow y →
          x = y) ∧
      compactUniformRadiusChoiceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · exact CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          CompactUniformRadiusChoiceTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.CompactUniformRadiusChoiceUp
