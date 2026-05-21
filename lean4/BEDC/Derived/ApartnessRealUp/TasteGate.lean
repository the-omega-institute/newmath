import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessRealUp : Type where
  | mk (left right radius window leftReadback rightReadback : BHist) : ApartnessRealUp
  deriving DecidableEq

def apartnessRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessRealEncodeBHist h

def apartnessRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessRealDecodeBHist tail)

private theorem ApartnessRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, apartnessRealDecodeBHist (apartnessRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ApartnessRealTasteGate_single_carrier_alignment_fields :
    ApartnessRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessRealUp.mk left right radius window leftReadback rightReadback =>
      [left, right, radius, window, leftReadback, rightReadback]

def apartnessRealToEventFlow : ApartnessRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessRealUp.mk left right radius window leftReadback rightReadback =>
      [apartnessRealEncodeBHist left, apartnessRealEncodeBHist right,
        apartnessRealEncodeBHist radius, apartnessRealEncodeBHist window,
        apartnessRealEncodeBHist leftReadback, apartnessRealEncodeBHist rightReadback]

def apartnessRealFromEventFlow : EventFlow → Option ApartnessRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | left :: right :: radius :: window :: leftReadback :: rightReadback :: [] =>
      some
        (ApartnessRealUp.mk
          (apartnessRealDecodeBHist left)
          (apartnessRealDecodeBHist right)
          (apartnessRealDecodeBHist radius)
          (apartnessRealDecodeBHist window)
          (apartnessRealDecodeBHist leftReadback)
          (apartnessRealDecodeBHist rightReadback))
  | _ => none

private theorem ApartnessRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ApartnessRealUp,
      apartnessRealFromEventFlow (apartnessRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right radius window leftReadback rightReadback =>
      rw [apartnessRealToEventFlow, apartnessRealFromEventFlow,
        ApartnessRealTasteGate_single_carrier_alignment_decode left,
        ApartnessRealTasteGate_single_carrier_alignment_decode right,
        ApartnessRealTasteGate_single_carrier_alignment_decode radius,
        ApartnessRealTasteGate_single_carrier_alignment_decode window,
        ApartnessRealTasteGate_single_carrier_alignment_decode leftReadback,
        ApartnessRealTasteGate_single_carrier_alignment_decode rightReadback]

private theorem ApartnessRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ApartnessRealUp} :
    apartnessRealToEventFlow x = apartnessRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessRealFromEventFlow (apartnessRealToEventFlow x) =
        apartnessRealFromEventFlow (apartnessRealToEventFlow y) :=
    congrArg apartnessRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ApartnessRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ApartnessRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem ApartnessRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ApartnessRealUp,
      ApartnessRealTasteGate_single_carrier_alignment_fields x =
          ApartnessRealTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk left₁ right₁ radius₁ window₁ leftReadback₁ rightReadback₁ =>
      cases y with
      | mk left₂ right₂ radius₂ window₂ leftReadback₂ rightReadback₂ =>
          injection hfields with hLeft tail0
          injection tail0 with hRight tail1
          injection tail1 with hRadius tail2
          injection tail2 with hWindow tail3
          injection tail3 with hLeftReadback tail4
          injection tail4 with hRightReadback _
          subst hLeft
          subst hRight
          subst hRadius
          subst hWindow
          subst hLeftReadback
          subst hRightReadback
          rfl

instance apartnessRealBHistCarrier : BHistCarrier ApartnessRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessRealToEventFlow
  fromEventFlow := apartnessRealFromEventFlow

instance apartnessRealChapterTasteGate : ChapterTasteGate ApartnessRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apartnessRealFromEventFlow (apartnessRealToEventFlow x) = some x
    exact ApartnessRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ApartnessRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance apartnessRealFieldFaithful : FieldFaithful ApartnessRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ApartnessRealTasteGate_single_carrier_alignment_fields
  field_faithful := ApartnessRealTasteGate_single_carrier_alignment_fields_faithful

instance apartnessRealNontrivial : Nontrivial ApartnessRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApartnessRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ApartnessRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ApartnessRealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ApartnessRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apartnessRealChapterTasteGate

theorem ApartnessRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, apartnessRealDecodeBHist (apartnessRealEncodeBHist h) = h) ∧
      ApartnessRealTasteGate_single_carrier_alignment_fields
          (ApartnessRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ApartnessRealTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.ApartnessRealUp
