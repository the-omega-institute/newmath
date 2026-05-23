import BEDC.Derived.PermutationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PermutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PermutationUp : Type where
  | mk (src tgt graph invGraph inverseWitness classifier action ledger : BHist) : PermutationUp
  deriving DecidableEq

def permutationTasteGateTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def permutationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: permutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: permutationEncodeBHist h

def permutationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (permutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (permutationDecodeBHist tail)

private theorem PermutationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, permutationDecodeBHist (permutationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def permutationFields : PermutationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PermutationUp.mk src tgt graph invGraph inverseWitness classifier action ledger =>
      [src, tgt, graph, invGraph, inverseWitness, classifier, action, ledger]

def permutationToEventFlow : PermutationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PermutationUp.mk src tgt graph invGraph inverseWitness classifier action ledger =>
      [permutationTasteGateTag,
        permutationEncodeBHist src,
        permutationEncodeBHist tgt,
        permutationEncodeBHist graph,
        permutationEncodeBHist invGraph,
        permutationEncodeBHist inverseWitness,
        permutationEncodeBHist classifier,
        permutationEncodeBHist action,
        permutationEncodeBHist ledger]

private def PermutationTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      PermutationTasteGate_single_carrier_alignment_eventAt index rest

def permutationFromEventFlow : EventFlow → Option PermutationUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PermutationUp.mk
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 1 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 2 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 3 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 4 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 5 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 6 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 7 ef))
          (permutationDecodeBHist (PermutationTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem PermutationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PermutationUp, permutationFromEventFlow (permutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk src tgt graph invGraph inverseWitness classifier action ledger =>
      change
        some
          (PermutationUp.mk
            (permutationDecodeBHist (permutationEncodeBHist src))
            (permutationDecodeBHist (permutationEncodeBHist tgt))
            (permutationDecodeBHist (permutationEncodeBHist graph))
            (permutationDecodeBHist (permutationEncodeBHist invGraph))
            (permutationDecodeBHist (permutationEncodeBHist inverseWitness))
            (permutationDecodeBHist (permutationEncodeBHist classifier))
            (permutationDecodeBHist (permutationEncodeBHist action))
            (permutationDecodeBHist (permutationEncodeBHist ledger))) =
          some (PermutationUp.mk src tgt graph invGraph inverseWitness classifier action ledger)
      rw [PermutationTasteGate_single_carrier_alignment_decode_encode src,
        PermutationTasteGate_single_carrier_alignment_decode_encode tgt,
        PermutationTasteGate_single_carrier_alignment_decode_encode graph,
        PermutationTasteGate_single_carrier_alignment_decode_encode invGraph,
        PermutationTasteGate_single_carrier_alignment_decode_encode inverseWitness,
        PermutationTasteGate_single_carrier_alignment_decode_encode classifier,
        PermutationTasteGate_single_carrier_alignment_decode_encode action,
        PermutationTasteGate_single_carrier_alignment_decode_encode ledger]

private theorem PermutationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PermutationUp} :
    permutationToEventFlow x = permutationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      permutationFromEventFlow (permutationToEventFlow x) =
        permutationFromEventFlow (permutationToEventFlow y) :=
    congrArg permutationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PermutationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PermutationTasteGate_single_carrier_alignment_round_trip y)))

private theorem PermutationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PermutationUp, permutationFields x = permutationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk src₁ tgt₁ graph₁ invGraph₁ inverseWitness₁ classifier₁ action₁ ledger₁ =>
      cases y with
      | mk src₂ tgt₂ graph₂ invGraph₂ inverseWitness₂ classifier₂ action₂ ledger₂ =>
          cases hfields
          rfl

instance permutationBHistCarrier : BHistCarrier PermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := permutationToEventFlow
  fromEventFlow := permutationFromEventFlow

instance permutationChapterTasteGate : ChapterTasteGate PermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := PermutationTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (PermutationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance permutationFieldFaithful : FieldFaithful PermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := permutationFields
  field_faithful := PermutationTasteGate_single_carrier_alignment_fields_faithful

theorem PermutationTasteGate_single_carrier_alignment :
    (∀ h : BHist, permutationDecodeBHist (permutationEncodeBHist h) = h) ∧
      (∀ x : PermutationUp, permutationFromEventFlow (permutationToEventFlow x) = some x) ∧
        (∀ x y : PermutationUp, permutationToEventFlow x = permutationToEventFlow y →
          x = y) ∧
          permutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PermutationTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PermutationTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y
        exact PermutationTasteGate_single_carrier_alignment_toEventFlow_injective
      · rfl

end BEDC.Derived.PermutationUp
