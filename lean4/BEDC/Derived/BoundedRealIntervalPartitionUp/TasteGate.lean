import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRealIntervalPartitionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRealIntervalPartitionUp : Type where
  | mk (E S M T Q R L H C P N : BHist) : BoundedRealIntervalPartitionUp
  deriving DecidableEq

def boundedRealIntervalPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRealIntervalPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRealIntervalPartitionEncodeBHist h

def boundedRealIntervalPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRealIntervalPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRealIntervalPartitionDecodeBHist tail)

private theorem BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRealIntervalPartitionFields : BoundedRealIntervalPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealIntervalPartitionUp.mk E S M T Q R L H C P N => [E, S, M, T, Q, R, L, H, C, P, N]

def boundedRealIntervalPartitionToEventFlow : BoundedRealIntervalPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedRealIntervalPartitionFields x).map boundedRealIntervalPartitionEncodeBHist

private def boundedRealIntervalPartitionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedRealIntervalPartitionEventAt index rest

def boundedRealIntervalPartitionFromEventFlow
    (ef : EventFlow) : Option BoundedRealIntervalPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedRealIntervalPartitionUp.mk
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 0 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 1 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 2 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 3 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 4 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 5 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 6 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 7 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 8 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 9 ef))
      (boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEventAt 10 ef)))

private theorem BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip
    (x : BoundedRealIntervalPartitionUp) :
    boundedRealIntervalPartitionFromEventFlow (boundedRealIntervalPartitionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E S M T Q R L H C P N =>
      change
        some
          (BoundedRealIntervalPartitionUp.mk
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist E))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist S))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist M))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist T))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist Q))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist R))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist L))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist H))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist C))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist P))
            (boundedRealIntervalPartitionDecodeBHist
              (boundedRealIntervalPartitionEncodeBHist N))) =
          some (BoundedRealIntervalPartitionUp.mk E S M T Q R L H C P N)
      rw [BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode E,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode S,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode M,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode T,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode Q,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode R,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode L,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode H,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode C,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode P,
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedRealIntervalPartitionUp} :
    boundedRealIntervalPartitionToEventFlow x =
      boundedRealIntervalPartitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRealIntervalPartitionFromEventFlow (boundedRealIntervalPartitionToEventFlow x) =
        boundedRealIntervalPartitionFromEventFlow (boundedRealIntervalPartitionToEventFlow y) :=
    congrArg boundedRealIntervalPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BoundedRealIntervalPartitionUp,
      boundedRealIntervalPartitionFields x = boundedRealIntervalPartitionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ S₁ M₁ T₁ Q₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ S₂ M₂ T₂ Q₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundedRealIntervalPartitionBHistCarrier :
    BHistCarrier BoundedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRealIntervalPartitionToEventFlow
  fromEventFlow := boundedRealIntervalPartitionFromEventFlow

instance boundedRealIntervalPartitionChapterTasteGate :
    ChapterTasteGate BoundedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRealIntervalPartitionFromEventFlow
      (boundedRealIntervalPartitionToEventFlow x) = some x
    exact BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedRealIntervalPartitionFieldFaithful :
    FieldFaithful BoundedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedRealIntervalPartitionFields
  field_faithful := BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_fields_faithful

instance boundedRealIntervalPartitionNontrivial :
    Nontrivial BoundedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRealIntervalPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedRealIntervalPartitionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BoundedRealIntervalPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRealIntervalPartitionChapterTasteGate

theorem BoundedRealIntervalPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedRealIntervalPartitionDecodeBHist (boundedRealIntervalPartitionEncodeBHist h) = h) ∧
      (∀ x : BoundedRealIntervalPartitionUp,
        boundedRealIntervalPartitionFromEventFlow (boundedRealIntervalPartitionToEventFlow x) =
          some x) ∧
        (∀ x y : BoundedRealIntervalPartitionUp,
          boundedRealIntervalPartitionToEventFlow x =
              boundedRealIntervalPartitionToEventFlow y →
            x = y) ∧
          boundedRealIntervalPartitionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode,
      BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedRealIntervalPartitionUp.TasteGate
