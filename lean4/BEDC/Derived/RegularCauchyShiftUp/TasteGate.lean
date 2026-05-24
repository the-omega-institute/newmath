import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyShiftUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyShiftUp : Type where
  | mk (Q S D k E H C P N : BHist) : RegularCauchyShiftUp
  deriving DecidableEq

def regularCauchyShiftEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyShiftEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyShiftEncodeBHist h

def regularCauchyShiftDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyShiftDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyShiftDecodeBHist tail)

private theorem RegularCauchyShiftTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchyShiftDecodeBHist (regularCauchyShiftEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyShiftTasteGate_single_carrier_alignment_fields :
    RegularCauchyShiftUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyShiftUp.mk Q S D k E H C P N => [Q, S, D, k, E, H, C, P, N]

def regularCauchyShiftToEventFlow : RegularCauchyShiftUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyShiftUp.mk Q S D k E H C P N =>
      [regularCauchyShiftEncodeBHist Q, regularCauchyShiftEncodeBHist S,
        regularCauchyShiftEncodeBHist D, regularCauchyShiftEncodeBHist k,
        regularCauchyShiftEncodeBHist E, regularCauchyShiftEncodeBHist H,
        regularCauchyShiftEncodeBHist C, regularCauchyShiftEncodeBHist P,
        regularCauchyShiftEncodeBHist N]

def regularCauchyShiftFromEventFlow : EventFlow → Option RegularCauchyShiftUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: S :: D :: k :: E :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyShiftUp.mk
          (regularCauchyShiftDecodeBHist Q)
          (regularCauchyShiftDecodeBHist S)
          (regularCauchyShiftDecodeBHist D)
          (regularCauchyShiftDecodeBHist k)
          (regularCauchyShiftDecodeBHist E)
          (regularCauchyShiftDecodeBHist H)
          (regularCauchyShiftDecodeBHist C)
          (regularCauchyShiftDecodeBHist P)
          (regularCauchyShiftDecodeBHist N))
  | _ => none

private theorem RegularCauchyShiftTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyShiftUp,
      regularCauchyShiftFromEventFlow (regularCauchyShiftToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S D k E H C P N =>
      rw [regularCauchyShiftToEventFlow, regularCauchyShiftFromEventFlow,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode S,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode D,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode k,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode E,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode H,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode C,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode P,
        RegularCauchyShiftTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyShiftTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyShiftUp} :
    regularCauchyShiftToEventFlow x = regularCauchyShiftToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyShiftFromEventFlow (regularCauchyShiftToEventFlow x) =
        regularCauchyShiftFromEventFlow (regularCauchyShiftToEventFlow y) :=
    congrArg regularCauchyShiftFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyShiftTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyShiftTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyShiftTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyShiftUp,
      RegularCauchyShiftTasteGate_single_carrier_alignment_fields x =
          RegularCauchyShiftTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ S₁ D₁ k₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ S₂ D₂ k₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hQ tail0
          injection tail0 with hS tail1
          injection tail1 with hD tail2
          injection tail2 with hk tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hQ
          subst hS
          subst hD
          subst hk
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyShiftBHistCarrier : BHistCarrier RegularCauchyShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyShiftToEventFlow
  fromEventFlow := regularCauchyShiftFromEventFlow

instance regularCauchyShiftChapterTasteGate : ChapterTasteGate RegularCauchyShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyShiftFromEventFlow (regularCauchyShiftToEventFlow x) = some x
    exact RegularCauchyShiftTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyShiftTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyShiftFieldFaithful : FieldFaithful RegularCauchyShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegularCauchyShiftTasteGate_single_carrier_alignment_fields
  field_faithful := RegularCauchyShiftTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyShiftNontrivial : Nontrivial RegularCauchyShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyShiftUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyShiftUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchyShiftTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyShiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyShiftChapterTasteGate

theorem RegularCauchyShiftTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyShiftDecodeBHist (regularCauchyShiftEncodeBHist h) = h) ∧
      RegularCauchyShiftTasteGate_single_carrier_alignment_fields
          (RegularCauchyShiftUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyShiftTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.RegularCauchyShiftUp
