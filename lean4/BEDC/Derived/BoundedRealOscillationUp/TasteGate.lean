import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRealOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRealOscillationUp : Type where
  | mk (K F U A B R H C P N : BHist) : BoundedRealOscillationUp
  deriving DecidableEq

def boundedRealOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRealOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRealOscillationEncodeBHist h

def boundedRealOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRealOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRealOscillationDecodeBHist tail)

private theorem BoundedRealOscillationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BoundedRealOscillationTasteGate_single_carrier_alignment_fields :
    BoundedRealOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealOscillationUp.mk K F U A B R H C P N => [K, F, U, A, B, R, H, C, P, N]

def boundedRealOscillationToEventFlow : BoundedRealOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealOscillationUp.mk K F U A B R H C P N =>
      [boundedRealOscillationEncodeBHist K, boundedRealOscillationEncodeBHist F,
        boundedRealOscillationEncodeBHist U, boundedRealOscillationEncodeBHist A,
        boundedRealOscillationEncodeBHist B, boundedRealOscillationEncodeBHist R,
        boundedRealOscillationEncodeBHist H, boundedRealOscillationEncodeBHist C,
        boundedRealOscillationEncodeBHist P, boundedRealOscillationEncodeBHist N]

private def BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest =>
      BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt n rest

private def BoundedRealOscillationTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest =>
      BoundedRealOscillationTasteGate_single_carrier_alignment_lengthEq n rest

def boundedRealOscillationFromEventFlow : EventFlow → Option BoundedRealOscillationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match BoundedRealOscillationTasteGate_single_carrier_alignment_lengthEq 10 flow with
      | true =>
          some
            (BoundedRealOscillationUp.mk
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 0 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 1 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 2 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 3 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 4 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 5 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 6 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 7 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 8 flow))
              (boundedRealOscillationDecodeBHist
                (BoundedRealOscillationTasteGate_single_carrier_alignment_rawAt 9 flow)))
      | false => none

private theorem BoundedRealOscillationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedRealOscillationUp,
      boundedRealOscillationFromEventFlow (boundedRealOscillationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F U A B R H C P N =>
      change
        some
          (BoundedRealOscillationUp.mk
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist K))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist F))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist U))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist A))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist B))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist R))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist H))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist C))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist P))
            (boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist N))) =
          some (BoundedRealOscillationUp.mk K F U A B R H C P N)
      rw [BoundedRealOscillationTasteGate_single_carrier_alignment_decode K,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode F,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode U,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode A,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode B,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode R,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode H,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode C,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode P,
        BoundedRealOscillationTasteGate_single_carrier_alignment_decode N]

private theorem BoundedRealOscillationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedRealOscillationUp} :
    boundedRealOscillationToEventFlow x = boundedRealOscillationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRealOscillationFromEventFlow (boundedRealOscillationToEventFlow x) =
        boundedRealOscillationFromEventFlow (boundedRealOscillationToEventFlow y) :=
    congrArg boundedRealOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedRealOscillationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedRealOscillationTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedRealOscillationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BoundedRealOscillationUp,
      BoundedRealOscillationTasteGate_single_carrier_alignment_fields x =
          BoundedRealOscillationTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ U₁ A₁ B₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ U₂ A₂ B₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hF tail1
          injection tail1 with hU tail2
          injection tail2 with hA tail3
          injection tail3 with hB tail4
          injection tail4 with hR tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hK
          subst hF
          subst hU
          subst hA
          subst hB
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance boundedRealOscillationBHistCarrier : BHistCarrier BoundedRealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRealOscillationToEventFlow
  fromEventFlow := boundedRealOscillationFromEventFlow

instance boundedRealOscillationChapterTasteGate :
    ChapterTasteGate BoundedRealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRealOscillationFromEventFlow (boundedRealOscillationToEventFlow x) = some x
    exact BoundedRealOscillationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedRealOscillationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedRealOscillationFieldFaithful : FieldFaithful BoundedRealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BoundedRealOscillationTasteGate_single_carrier_alignment_fields
  field_faithful := BoundedRealOscillationTasteGate_single_carrier_alignment_fields_faithful

instance boundedRealOscillationNontrivial : Nontrivial BoundedRealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRealOscillationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedRealOscillationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def BoundedRealOscillationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BoundedRealOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRealOscillationChapterTasteGate

theorem BoundedRealOscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedRealOscillationDecodeBHist (boundedRealOscillationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BoundedRealOscillationUp) ∧
        Nonempty (ChapterTasteGate BoundedRealOscillationUp) ∧
          boundedRealOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BoundedRealOscillationTasteGate_single_carrier_alignment_decode,
      ⟨boundedRealOscillationBHistCarrier⟩,
      ⟨boundedRealOscillationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BoundedRealOscillationUp
