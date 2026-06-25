import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedCauchySequenceUp : Type where
  | mk (M S R T L H C P N : BHist) : BoundedCauchySequenceUp
  deriving DecidableEq

def boundedCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedCauchySequenceEncodeBHist h

def boundedCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedCauchySequenceDecodeBHist tail)

private theorem boundedCauchySequenceDecode_encode :
    ∀ h : BHist,
      boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedCauchySequenceFields : BoundedCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCauchySequenceUp.mk M S R T L H C P N => [M, S, R, T, L, H, C, P, N]

def boundedCauchySequenceToEventFlow : BoundedCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCauchySequenceUp.mk M S R T L H C P N =>
      [boundedCauchySequenceEncodeBHist M,
        boundedCauchySequenceEncodeBHist S,
        boundedCauchySequenceEncodeBHist R,
        boundedCauchySequenceEncodeBHist T,
        boundedCauchySequenceEncodeBHist L,
        boundedCauchySequenceEncodeBHist H,
        boundedCauchySequenceEncodeBHist C,
        boundedCauchySequenceEncodeBHist P,
        boundedCauchySequenceEncodeBHist N]

private def boundedCauchySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedCauchySequenceEventAt index rest

def boundedCauchySequenceFromEventFlow : EventFlow → Option BoundedCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BoundedCauchySequenceUp.mk
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 0 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 1 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 2 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 3 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 4 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 5 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 6 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 7 ef))
        (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEventAt 8 ef)))

private theorem boundedCauchySequence_round_trip :
    ∀ x : BoundedCauchySequenceUp,
      boundedCauchySequenceFromEventFlow (boundedCauchySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S R T L H C P N =>
      change
        some
            (BoundedCauchySequenceUp.mk
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist M))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist S))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist R))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist T))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist L))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist H))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist C))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist P))
              (boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist N))) =
          some (BoundedCauchySequenceUp.mk M S R T L H C P N)
      rw [boundedCauchySequenceDecode_encode M, boundedCauchySequenceDecode_encode S,
        boundedCauchySequenceDecode_encode R, boundedCauchySequenceDecode_encode T,
        boundedCauchySequenceDecode_encode L, boundedCauchySequenceDecode_encode H,
        boundedCauchySequenceDecode_encode C, boundedCauchySequenceDecode_encode P,
        boundedCauchySequenceDecode_encode N]

private theorem boundedCauchySequenceToEventFlow_injective {x y : BoundedCauchySequenceUp} :
    boundedCauchySequenceToEventFlow x = boundedCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedCauchySequenceFromEventFlow (boundedCauchySequenceToEventFlow x) =
        boundedCauchySequenceFromEventFlow (boundedCauchySequenceToEventFlow y) :=
    congrArg boundedCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedCauchySequence_round_trip x).symm
      (Eq.trans hread (boundedCauchySequence_round_trip y)))

private theorem boundedCauchySequence_fields_faithful :
    ∀ x y : BoundedCauchySequenceUp,
      boundedCauchySequenceFields x = boundedCauchySequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ S₁ R₁ T₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ S₂ R₂ T₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundedCauchySequenceBHistCarrier : BHistCarrier BoundedCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedCauchySequenceToEventFlow
  fromEventFlow := boundedCauchySequenceFromEventFlow

instance boundedCauchySequenceChapterTasteGate :
    ChapterTasteGate BoundedCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedCauchySequenceFromEventFlow (boundedCauchySequenceToEventFlow x) = some x
    exact boundedCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedCauchySequenceToEventFlow_injective heq)

instance boundedCauchySequenceFieldFaithful : FieldFaithful BoundedCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedCauchySequenceFields
  field_faithful := boundedCauchySequence_fields_faithful

instance boundedCauchySequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BoundedCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedCauchySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedCauchySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedCauchySequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedCauchySequenceUp) ∧
      Nonempty (FieldFaithful BoundedCauchySequenceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedCauchySequenceUp) ∧
      (∀ h : BHist,
        boundedCauchySequenceDecodeBHist (boundedCauchySequenceEncodeBHist h) = h) ∧
      (∀ x : BoundedCauchySequenceUp,
        boundedCauchySequenceFromEventFlow (boundedCauchySequenceToEventFlow x) = some x) ∧
      boundedCauchySequenceEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact ⟨boundedCauchySequenceChapterTasteGate⟩
  constructor
  · exact ⟨boundedCauchySequenceFieldFaithful⟩
  constructor
  · exact ⟨boundedCauchySequenceNontrivial⟩
  constructor
  · exact boundedCauchySequenceDecode_encode
  constructor
  · exact boundedCauchySequence_round_trip
  · rfl

end BEDC.Derived.BoundedCauchySequenceUp
