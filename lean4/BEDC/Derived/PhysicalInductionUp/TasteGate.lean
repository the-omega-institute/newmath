import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalInductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalInductionUp : Type where
  | mk : (O H A S B F T R P N : BHist) -> PhysicalInductionUp
  deriving DecidableEq

def physicalInductionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalInductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalInductionEncodeBHist h

def physicalInductionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalInductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalInductionDecodeBHist tail)

private theorem physicalInductionDecode_encode_bhist :
    ∀ h : BHist, physicalInductionDecodeBHist (physicalInductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def physicalInductionFields : PhysicalInductionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalInductionUp.mk O H A S B F T R P N => [O, H, A, S, B, F, T, R, P, N]

def physicalInductionToEventFlow : PhysicalInductionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (physicalInductionFields x).map physicalInductionEncodeBHist

private def physicalInductionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => physicalInductionEventAtDefault index rest

def physicalInductionFromEventFlow : EventFlow -> Option PhysicalInductionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PhysicalInductionUp.mk
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 0 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 1 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 2 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 3 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 4 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 5 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 6 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 7 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 8 ef))
          (physicalInductionDecodeBHist (physicalInductionEventAtDefault 9 ef)))

private theorem physicalInduction_round_trip :
    ∀ x : PhysicalInductionUp,
      physicalInductionFromEventFlow (physicalInductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O H A S B F T R P N =>
      change
        some
            (PhysicalInductionUp.mk
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist O))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist H))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist A))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist S))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist B))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist F))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist T))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist R))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist P))
              (physicalInductionDecodeBHist (physicalInductionEncodeBHist N))) =
          some (PhysicalInductionUp.mk O H A S B F T R P N)
      rw [physicalInductionDecode_encode_bhist O, physicalInductionDecode_encode_bhist H,
        physicalInductionDecode_encode_bhist A, physicalInductionDecode_encode_bhist S,
        physicalInductionDecode_encode_bhist B, physicalInductionDecode_encode_bhist F,
        physicalInductionDecode_encode_bhist T, physicalInductionDecode_encode_bhist R,
        physicalInductionDecode_encode_bhist P, physicalInductionDecode_encode_bhist N]

private theorem physicalInductionToEventFlow_injective {x y : PhysicalInductionUp} :
    physicalInductionToEventFlow x = physicalInductionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalInductionFromEventFlow (physicalInductionToEventFlow x) =
        physicalInductionFromEventFlow (physicalInductionToEventFlow y) :=
    congrArg physicalInductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalInduction_round_trip x).symm
      (Eq.trans hread (physicalInduction_round_trip y)))

private theorem physicalInduction_field_faithful :
    ∀ x y : PhysicalInductionUp, physicalInductionFields x = physicalInductionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O H A S B F T R P N =>
      cases y with
      | mk O' H' A' S' B' F' T' R' P' N' =>
          cases hfields
          rfl

instance physicalInductionBHistCarrier : BHistCarrier PhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalInductionToEventFlow
  fromEventFlow := physicalInductionFromEventFlow

instance physicalInductionChapterTasteGate : ChapterTasteGate PhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicalInductionFromEventFlow (physicalInductionToEventFlow x) = some x
    exact physicalInduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalInductionToEventFlow_injective heq)

instance physicalInductionFieldFaithful : FieldFaithful PhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalInductionFields
  field_faithful := physicalInduction_field_faithful

instance physicalInductionNontrivial : Nontrivial PhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalInductionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalInductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalInductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalInductionChapterTasteGate

theorem PhysicalInductionTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicalInductionDecodeBHist (physicalInductionEncodeBHist h) = h) ∧
      (∀ x : PhysicalInductionUp,
        physicalInductionFromEventFlow (physicalInductionToEventFlow x) = some x) ∧
        (∀ x y : PhysicalInductionUp,
          physicalInductionToEventFlow x = physicalInductionToEventFlow y -> x = y) ∧
          physicalInductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact physicalInductionDecode_encode_bhist
  · constructor
    · exact physicalInduction_round_trip
    · constructor
      · intro x y hxy
        exact physicalInductionToEventFlow_injective hxy
      · rfl

end BEDC.Derived.PhysicalInductionUp
