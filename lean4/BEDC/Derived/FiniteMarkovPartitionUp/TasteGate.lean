import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteMarkovPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteMarkovPartitionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (P B J R T H C S N : BHist) : FiniteMarkovPartitionUp
  deriving DecidableEq

def finiteMarkovPartitionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteMarkovPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteMarkovPartitionEncodeBHist h

def finiteMarkovPartitionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteMarkovPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteMarkovPartitionDecodeBHist tail)

private theorem FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteMarkovPartitionFields : FiniteMarkovPartitionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMarkovPartitionUp.mk P B J R T H C S N => [P, B, J, R, T, H, C, S, N]

def finiteMarkovPartitionToEventFlow : FiniteMarkovPartitionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteMarkovPartitionFields x).map finiteMarkovPartitionEncodeBHist

def finiteMarkovPartitionFromEventFlow : EventFlow -> Option FiniteMarkovPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | P :: B :: J :: R :: T :: H :: C :: S :: N :: [] =>
      some
        (FiniteMarkovPartitionUp.mk
          (finiteMarkovPartitionDecodeBHist P)
          (finiteMarkovPartitionDecodeBHist B)
          (finiteMarkovPartitionDecodeBHist J)
          (finiteMarkovPartitionDecodeBHist R)
          (finiteMarkovPartitionDecodeBHist T)
          (finiteMarkovPartitionDecodeBHist H)
          (finiteMarkovPartitionDecodeBHist C)
          (finiteMarkovPartitionDecodeBHist S)
          (finiteMarkovPartitionDecodeBHist N))
  | _ => none

private theorem FiniteMarkovPartitionTasteGate_single_carrier_alignment_round_trip
    (x : FiniteMarkovPartitionUp) :
    finiteMarkovPartitionFromEventFlow (finiteMarkovPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P B J R T H C S N =>
      change
        some
          (FiniteMarkovPartitionUp.mk
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist P))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist B))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist J))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist R))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist T))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist H))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist C))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist S))
            (finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist N))) =
          some (FiniteMarkovPartitionUp.mk P B J R T H C S N)
      rw [FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode P,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode B,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode J,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode R,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode T,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode H,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode C,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode S,
        FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteMarkovPartitionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteMarkovPartitionUp} :
    finiteMarkovPartitionToEventFlow x = finiteMarkovPartitionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteMarkovPartitionFromEventFlow (finiteMarkovPartitionToEventFlow x) =
        finiteMarkovPartitionFromEventFlow (finiteMarkovPartitionToEventFlow y) :=
    congrArg finiteMarkovPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteMarkovPartitionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteMarkovPartitionTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteMarkovPartitionTasteGate_single_carrier_alignment_fields_faithful
    (x y : FiniteMarkovPartitionUp) :
    finiteMarkovPartitionFields x = finiteMarkovPartitionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk P₁ B₁ J₁ R₁ T₁ H₁ C₁ S₁ N₁ =>
      cases y with
      | mk P₂ B₂ J₂ R₂ T₂ H₂ C₂ S₂ N₂ =>
          injection h with hP hRest₁
          injection hRest₁ with hB hRest₂
          injection hRest₂ with hJ hRest₃
          injection hRest₃ with hR hRest₄
          injection hRest₄ with hT hRest₅
          injection hRest₅ with hH hRest₆
          injection hRest₆ with hC hRest₇
          injection hRest₇ with hS hRest₈
          injection hRest₈ with hN _
          subst hP
          subst hB
          subst hJ
          subst hR
          subst hT
          subst hH
          subst hC
          subst hS
          subst hN
          rfl

instance finiteMarkovPartitionBHistCarrier : BHistCarrier FiniteMarkovPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteMarkovPartitionToEventFlow
  fromEventFlow := finiteMarkovPartitionFromEventFlow

instance finiteMarkovPartitionChapterTasteGate : ChapterTasteGate FiniteMarkovPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (FiniteMarkovPartitionTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteMarkovPartitionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteMarkovPartitionFieldFaithful : FieldFaithful FiniteMarkovPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteMarkovPartitionFields
  field_faithful := FiniteMarkovPartitionTasteGate_single_carrier_alignment_fields_faithful

instance finiteMarkovPartitionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteMarkovPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteMarkovPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteMarkovPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteMarkovPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteMarkovPartitionDecodeBHist (finiteMarkovPartitionEncodeBHist h) = h) ∧
      finiteMarkovPartitionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteMarkovPartitionTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.FiniteMarkovPartitionUp
