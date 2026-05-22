import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyInterpolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyInterpolationUp : Type where
  | mk (R D M W S E H C P N : BHist) : RegularCauchyInterpolationUp
  deriving DecidableEq

def regularCauchyInterpolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyInterpolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyInterpolationEncodeBHist h

def regularCauchyInterpolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyInterpolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyInterpolationDecodeBHist tail)

private theorem RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyInterpolationDecodeBHist
          (regularCauchyInterpolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyInterpolationFields : RegularCauchyInterpolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyInterpolationUp.mk R D M W S E H C P N => [R, D, M, W, S, E, H, C, P, N]

def regularCauchyInterpolationToEventFlow : RegularCauchyInterpolationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyInterpolationFields x).map regularCauchyInterpolationEncodeBHist

def regularCauchyInterpolationFromEventFlow : EventFlow → Option RegularCauchyInterpolationUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: D :: M :: W :: S :: E :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyInterpolationUp.mk
          (regularCauchyInterpolationDecodeBHist R)
          (regularCauchyInterpolationDecodeBHist D)
          (regularCauchyInterpolationDecodeBHist M)
          (regularCauchyInterpolationDecodeBHist W)
          (regularCauchyInterpolationDecodeBHist S)
          (regularCauchyInterpolationDecodeBHist E)
          (regularCauchyInterpolationDecodeBHist H)
          (regularCauchyInterpolationDecodeBHist C)
          (regularCauchyInterpolationDecodeBHist P)
          (regularCauchyInterpolationDecodeBHist N))
  | _ => none

private theorem RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyInterpolationUp,
      regularCauchyInterpolationFromEventFlow
          (regularCauchyInterpolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R D M W S E H C P N =>
      change
        some
          (RegularCauchyInterpolationUp.mk
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist R))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist D))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist M))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist W))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist S))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist E))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist H))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist C))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist P))
            (regularCauchyInterpolationDecodeBHist
              (regularCauchyInterpolationEncodeBHist N))) =
          some (RegularCauchyInterpolationUp.mk R D M W S E H C P N)
      rw [RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyInterpolationUp} :
    regularCauchyInterpolationToEventFlow x = regularCauchyInterpolationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyInterpolationFromEventFlow (regularCauchyInterpolationToEventFlow x) =
        regularCauchyInterpolationFromEventFlow (regularCauchyInterpolationToEventFlow y) :=
    congrArg regularCauchyInterpolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyInterpolationUp,
      regularCauchyInterpolationFields x = regularCauchyInterpolationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ D₁ M₁ W₁ S₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ D₂ M₂ W₂ S₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hD tail1
          injection tail1 with hM tail2
          injection tail2 with hW tail3
          injection tail3 with hS tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hR
          subst hD
          subst hM
          subst hW
          subst hS
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyInterpolationBHistCarrier : BHistCarrier RegularCauchyInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyInterpolationToEventFlow
  fromEventFlow := regularCauchyInterpolationFromEventFlow

instance regularCauchyInterpolationChapterTasteGate :
    ChapterTasteGate RegularCauchyInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyInterpolationFromEventFlow (regularCauchyInterpolationToEventFlow x) =
        some x
    exact RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyInterpolationFieldFaithful : FieldFaithful RegularCauchyInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyInterpolationFields
  field_faithful :=
    RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyInterpolationNontrivial : Nontrivial RegularCauchyInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyInterpolationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyInterpolationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyInterpolationChapterTasteGate

theorem RegularCauchyInterpolationUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyInterpolationDecodeBHist (regularCauchyInterpolationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyInterpolationUp,
        regularCauchyInterpolationToEventFlow x =
          List.map regularCauchyInterpolationEncodeBHist
            (regularCauchyInterpolationFields x)) ∧
        (∀ x y : RegularCauchyInterpolationUp,
          regularCauchyInterpolationFields x = regularCauchyInterpolationFields y → x = y) ∧
          (∃ x y : RegularCauchyInterpolationUp, x ≠ y) ∧
            regularCauchyInterpolationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_decode_encode,
      by
        intro x
        cases x
        rfl,
      RegularCauchyInterpolationUpTasteGate_single_carrier_alignment_fields_faithful,
      ⟨RegularCauchyInterpolationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        RegularCauchyInterpolationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyInterpolationUp
