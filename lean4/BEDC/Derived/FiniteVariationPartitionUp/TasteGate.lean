import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteVariationPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteVariationPartitionUp : Type where
  | mk (I E P M D S T H C Q N : BHist) : FiniteVariationPartitionUp
  deriving DecidableEq

def finiteVariationPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteVariationPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteVariationPartitionEncodeBHist h

def finiteVariationPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteVariationPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteVariationPartitionDecodeBHist tail)

private theorem FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteVariationPartitionFields : FiniteVariationPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteVariationPartitionUp.mk I E P M D S T H C Q N => [I, E, P, M, D, S, T, H, C, Q, N]

def finiteVariationPartitionToEventFlow : FiniteVariationPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteVariationPartitionFields x).map finiteVariationPartitionEncodeBHist

private def finiteVariationPartitionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteVariationPartitionEventAt index rest

def finiteVariationPartitionFromEventFlow
    (ef : EventFlow) : Option FiniteVariationPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteVariationPartitionUp.mk
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 0 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 1 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 2 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 3 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 4 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 5 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 6 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 7 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 8 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 9 ef))
      (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEventAt 10 ef)))

private theorem FiniteVariationPartitionTasteGate_single_carrier_alignment_round_trip
    (x : FiniteVariationPartitionUp) :
    finiteVariationPartitionFromEventFlow (finiteVariationPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I E P M D S T H C Q N =>
      change
        some
          (FiniteVariationPartitionUp.mk
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist I))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist E))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist P))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist M))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist D))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist S))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist T))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist H))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist C))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist Q))
            (finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist N))) =
          some (FiniteVariationPartitionUp.mk I E P M D S T H C Q N)
      rw [FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode I,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode E,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode P,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode M,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode D,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode S,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode T,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode H,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode C,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode Q,
        FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteVariationPartitionTasteGate_single_carrier_alignment_injective
    {x y : FiniteVariationPartitionUp} :
    finiteVariationPartitionToEventFlow x = finiteVariationPartitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteVariationPartitionFromEventFlow (finiteVariationPartitionToEventFlow x) =
        finiteVariationPartitionFromEventFlow (finiteVariationPartitionToEventFlow y) :=
    congrArg finiteVariationPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteVariationPartitionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteVariationPartitionTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteVariationPartitionTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteVariationPartitionUp,
      finiteVariationPartitionFields x = finiteVariationPartitionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ E₁ P₁ M₁ D₁ S₁ T₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk I₂ E₂ P₂ M₂ D₂ S₂ T₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance finiteVariationPartitionBHistCarrier : BHistCarrier FiniteVariationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteVariationPartitionToEventFlow
  fromEventFlow := finiteVariationPartitionFromEventFlow

instance finiteVariationPartitionChapterTasteGate :
    ChapterTasteGate FiniteVariationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteVariationPartitionFromEventFlow (finiteVariationPartitionToEventFlow x) = some x
    exact FiniteVariationPartitionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteVariationPartitionTasteGate_single_carrier_alignment_injective heq)

instance finiteVariationPartitionFieldFaithful : FieldFaithful FiniteVariationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteVariationPartitionFields
  field_faithful := FiniteVariationPartitionTasteGate_single_carrier_alignment_fields

instance finiteVariationPartitionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteVariationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteVariationPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteVariationPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteVariationPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteVariationPartitionDecodeBHist (finiteVariationPartitionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteVariationPartitionUp) ∧
        Nonempty (ChapterTasteGate FiniteVariationPartitionUp) ∧
          Nonempty (FieldFaithful FiniteVariationPartitionUp) ∧
            (∃ x y : FiniteVariationPartitionUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact FiniteVariationPartitionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact ⟨finiteVariationPartitionBHistCarrier⟩
  constructor
  · exact ⟨finiteVariationPartitionChapterTasteGate⟩
  constructor
  · exact ⟨finiteVariationPartitionFieldFaithful⟩
  · exact
      ⟨FiniteVariationPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        FiniteVariationPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩

end BEDC.Derived.FiniteVariationPartitionUp
