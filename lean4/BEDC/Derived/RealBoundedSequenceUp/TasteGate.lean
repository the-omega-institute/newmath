import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBoundedSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBoundedSequenceUp : Type where
  | mk (S B W R E H C P N : BHist) : RealBoundedSequenceUp
  deriving DecidableEq

def realBoundedSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBoundedSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBoundedSequenceEncodeBHist h

def realBoundedSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBoundedSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBoundedSequenceDecodeBHist tail)

private theorem RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBoundedSequenceFields : RealBoundedSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBoundedSequenceUp.mk S B W R E H C P N => [S, B, W, R, E, H, C, P, N]

def realBoundedSequenceToEventFlow : RealBoundedSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realBoundedSequenceFields x).map realBoundedSequenceEncodeBHist

private def realBoundedSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realBoundedSequenceEventAt index rest

def realBoundedSequenceFromEventFlow (ef : EventFlow) : Option RealBoundedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealBoundedSequenceUp.mk
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 0 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 1 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 2 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 3 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 4 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 5 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 6 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 7 ef))
      (realBoundedSequenceDecodeBHist (realBoundedSequenceEventAt 8 ef)))

private theorem RealBoundedSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealBoundedSequenceUp,
      realBoundedSequenceFromEventFlow (realBoundedSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B W R E H C P N =>
      change
        some
          (RealBoundedSequenceUp.mk
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist S))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist B))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist W))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist R))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist E))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist H))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist C))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist P))
            (realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist N))) =
          some (RealBoundedSequenceUp.mk S B W R E H C P N)
      rw [RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode S,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode B,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode W,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode R,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode E,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode H,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode C,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode P,
        RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealBoundedSequenceUp} :
    realBoundedSequenceToEventFlow x = realBoundedSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBoundedSequenceFromEventFlow (realBoundedSequenceToEventFlow x) =
        realBoundedSequenceFromEventFlow (realBoundedSequenceToEventFlow y) :=
    congrArg realBoundedSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealBoundedSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealBoundedSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealBoundedSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealBoundedSequenceUp,
      realBoundedSequenceFields x = realBoundedSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ B₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ B₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realBoundedSequenceBHistCarrier : BHistCarrier RealBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBoundedSequenceToEventFlow
  fromEventFlow := realBoundedSequenceFromEventFlow

instance realBoundedSequenceChapterTasteGate : ChapterTasteGate RealBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBoundedSequenceFromEventFlow (realBoundedSequenceToEventFlow x) = some x
    exact RealBoundedSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realBoundedSequenceFieldFaithful : FieldFaithful RealBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realBoundedSequenceFields
  field_faithful := RealBoundedSequenceTasteGate_single_carrier_alignment_fields

instance realBoundedSequenceNontrivial : Nontrivial RealBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealBoundedSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealBoundedSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealBoundedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realBoundedSequenceChapterTasteGate

theorem RealBoundedSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, realBoundedSequenceDecodeBHist (realBoundedSequenceEncodeBHist h) = h) ∧
      (∀ x : RealBoundedSequenceUp,
        realBoundedSequenceFromEventFlow (realBoundedSequenceToEventFlow x) = some x) ∧
        (∀ x y : RealBoundedSequenceUp,
          realBoundedSequenceToEventFlow x = realBoundedSequenceToEventFlow y → x = y) ∧
          realBoundedSequenceFields
              (RealBoundedSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealBoundedSequenceTasteGate_single_carrier_alignment_decode_encode,
      RealBoundedSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealBoundedSequenceUp
