import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRegularCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRegularCauchyUp : Type where
  | mk (S M B Q A H C P N : BHist) : BoundedRegularCauchyUp
  deriving DecidableEq

def boundedRegularCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRegularCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRegularCauchyEncodeBHist h

def boundedRegularCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRegularCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRegularCauchyDecodeBHist tail)

private theorem BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRegularCauchyFields : BoundedRegularCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRegularCauchyUp.mk S M B Q A H C P N => [S, M, B, Q, A, H, C, P, N]

def boundedRegularCauchyToEventFlow : BoundedRegularCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedRegularCauchyFields x).map boundedRegularCauchyEncodeBHist

def boundedRegularCauchyFromEventFlow : EventFlow → Option BoundedRegularCauchyUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: M :: B :: Q :: A :: H :: C :: P :: N :: [] =>
      some
        (BoundedRegularCauchyUp.mk
          (boundedRegularCauchyDecodeBHist S)
          (boundedRegularCauchyDecodeBHist M)
          (boundedRegularCauchyDecodeBHist B)
          (boundedRegularCauchyDecodeBHist Q)
          (boundedRegularCauchyDecodeBHist A)
          (boundedRegularCauchyDecodeBHist H)
          (boundedRegularCauchyDecodeBHist C)
          (boundedRegularCauchyDecodeBHist P)
          (boundedRegularCauchyDecodeBHist N))
  | _ => none

private theorem BoundedRegularCauchyUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedRegularCauchyUp,
      boundedRegularCauchyFromEventFlow (boundedRegularCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M B Q A H C P N =>
      change
        some
          (BoundedRegularCauchyUp.mk
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist S))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist M))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist B))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist Q))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist A))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist H))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist C))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist P))
            (boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist N))) =
          some (BoundedRegularCauchyUp.mk S M B Q A H C P N)
      rw [BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode S,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode M,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode B,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode Q,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode A,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode H,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode C,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode P,
        BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedRegularCauchyUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedRegularCauchyUp} :
    boundedRegularCauchyToEventFlow x = boundedRegularCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRegularCauchyFromEventFlow (boundedRegularCauchyToEventFlow x) =
        boundedRegularCauchyFromEventFlow (boundedRegularCauchyToEventFlow y) :=
    congrArg boundedRegularCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedRegularCauchyUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedRegularCauchyUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedRegularCauchyUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BoundedRegularCauchyUp,
      boundedRegularCauchyFields x = boundedRegularCauchyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ B₁ Q₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ B₂ Q₂ A₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hM tail1
          injection tail1 with hB tail2
          injection tail2 with hQ tail3
          injection tail3 with hA tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hS
          subst hM
          subst hB
          subst hQ
          subst hA
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance boundedRegularCauchyBHistCarrier : BHistCarrier BoundedRegularCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRegularCauchyToEventFlow
  fromEventFlow := boundedRegularCauchyFromEventFlow

instance boundedRegularCauchyChapterTasteGate :
    ChapterTasteGate BoundedRegularCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRegularCauchyFromEventFlow (boundedRegularCauchyToEventFlow x) = some x
    exact BoundedRegularCauchyUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedRegularCauchyUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedRegularCauchyFieldFaithful : FieldFaithful BoundedRegularCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedRegularCauchyFields
  field_faithful := BoundedRegularCauchyUpTasteGate_single_carrier_alignment_fields_faithful

instance boundedRegularCauchyNontrivial : Nontrivial BoundedRegularCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRegularCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedRegularCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedRegularCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRegularCauchyChapterTasteGate

theorem BoundedRegularCauchyUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedRegularCauchyDecodeBHist (boundedRegularCauchyEncodeBHist h) = h) ∧
      (∀ x : BoundedRegularCauchyUp,
        boundedRegularCauchyToEventFlow x =
          List.map boundedRegularCauchyEncodeBHist (boundedRegularCauchyFields x)) ∧
        (∀ x y : BoundedRegularCauchyUp,
          boundedRegularCauchyFields x = boundedRegularCauchyFields y → x = y) ∧
          (∃ x y : BoundedRegularCauchyUp, x ≠ y) ∧
            boundedRegularCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BoundedRegularCauchyUpTasteGate_single_carrier_alignment_decode_encode,
      by
        intro x
        cases x
        rfl,
      BoundedRegularCauchyUpTasteGate_single_carrier_alignment_fields_faithful,
      ⟨BoundedRegularCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        BoundedRegularCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.BoundedRegularCauchyUp
