import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExtremeValueTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExtremeValueTheoremUp : Type where
  | mk (I K F R S W H C P N : BHist) : ExtremeValueTheoremUp
  deriving DecidableEq

def extremeValueTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: extremeValueTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: extremeValueTheoremEncodeBHist h

def extremeValueTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (extremeValueTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (extremeValueTheoremDecodeBHist tail)

private theorem ExtremeValueTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ExtremeValueTheoremTasteGate_single_carrier_alignment_fields :
    ExtremeValueTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExtremeValueTheoremUp.mk I K F R S W H C P N => [I, K, F, R, S, W, H, C, P, N]

def extremeValueTheoremToEventFlow : ExtremeValueTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ExtremeValueTheoremUp.mk I K F R S W H C P N =>
      [extremeValueTheoremEncodeBHist I, extremeValueTheoremEncodeBHist K,
        extremeValueTheoremEncodeBHist F, extremeValueTheoremEncodeBHist R,
        extremeValueTheoremEncodeBHist S, extremeValueTheoremEncodeBHist W,
        extremeValueTheoremEncodeBHist H, extremeValueTheoremEncodeBHist C,
        extremeValueTheoremEncodeBHist P, extremeValueTheoremEncodeBHist N]

private def ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt n rest

private def ExtremeValueTheoremTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => ExtremeValueTheoremTasteGate_single_carrier_alignment_lengthEq n rest

def extremeValueTheoremFromEventFlow : EventFlow → Option ExtremeValueTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match ExtremeValueTheoremTasteGate_single_carrier_alignment_lengthEq 10 flow with
      | true =>
          some
            (ExtremeValueTheoremUp.mk
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 0 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 1 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 2 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 3 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 4 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 5 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 6 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 7 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 8 flow))
              (extremeValueTheoremDecodeBHist
                (ExtremeValueTheoremTasteGate_single_carrier_alignment_rawAt 9 flow)))
      | false => none

private theorem ExtremeValueTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ExtremeValueTheoremUp,
      extremeValueTheoremFromEventFlow (extremeValueTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I K F R S W H C P N =>
      change
        some
          (ExtremeValueTheoremUp.mk
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist I))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist K))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist F))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist R))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist S))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist W))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist H))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist C))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist P))
            (extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist N))) =
          some (ExtremeValueTheoremUp.mk I K F R S W H C P N)
      rw [ExtremeValueTheoremTasteGate_single_carrier_alignment_decode I,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode K,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode F,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode R,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode S,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode W,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode H,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode C,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode P,
        ExtremeValueTheoremTasteGate_single_carrier_alignment_decode N]

private theorem ExtremeValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ExtremeValueTheoremUp} :
    extremeValueTheoremToEventFlow x = extremeValueTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      extremeValueTheoremFromEventFlow (extremeValueTheoremToEventFlow x) =
        extremeValueTheoremFromEventFlow (extremeValueTheoremToEventFlow y) :=
    congrArg extremeValueTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ExtremeValueTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ExtremeValueTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem ExtremeValueTheoremTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ExtremeValueTheoremUp,
      ExtremeValueTheoremTasteGate_single_carrier_alignment_fields x =
          ExtremeValueTheoremTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ K₁ F₁ R₁ S₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ K₂ F₂ R₂ S₂ W₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hI tail0
          injection tail0 with hK tail1
          injection tail1 with hF tail2
          injection tail2 with hR tail3
          injection tail3 with hS tail4
          injection tail4 with hW tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hI
          subst hK
          subst hF
          subst hR
          subst hS
          subst hW
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance extremeValueTheoremBHistCarrier : BHistCarrier ExtremeValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := extremeValueTheoremToEventFlow
  fromEventFlow := extremeValueTheoremFromEventFlow

instance extremeValueTheoremChapterTasteGate : ChapterTasteGate ExtremeValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change extremeValueTheoremFromEventFlow (extremeValueTheoremToEventFlow x) = some x
    exact ExtremeValueTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ExtremeValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance extremeValueTheoremFieldFaithful : FieldFaithful ExtremeValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ExtremeValueTheoremTasteGate_single_carrier_alignment_fields
  field_faithful := ExtremeValueTheoremTasteGate_single_carrier_alignment_fields_faithful

instance extremeValueTheoremNontrivial : Nontrivial ExtremeValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExtremeValueTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExtremeValueTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ExtremeValueTheoremTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ExtremeValueTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  extremeValueTheoremChapterTasteGate

theorem ExtremeValueTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, extremeValueTheoremDecodeBHist (extremeValueTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ExtremeValueTheoremUp) ∧
        Nonempty (ChapterTasteGate ExtremeValueTheoremUp) ∧
          extremeValueTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ExtremeValueTheoremTasteGate_single_carrier_alignment_decode,
      ⟨extremeValueTheoremBHistCarrier⟩,
      ⟨extremeValueTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ExtremeValueTheoremUp
