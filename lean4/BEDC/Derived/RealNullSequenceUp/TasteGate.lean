import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealNullSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealNullSequenceUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (S Z W R D L H C P N : BHist) : RealNullSequenceUp
  deriving DecidableEq

def realNullSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realNullSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realNullSequenceEncodeBHist h

def realNullSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realNullSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realNullSequenceDecodeBHist tail)

private theorem realNullSequence_decode_encode_bhist :
    ∀ h : BHist,
      realNullSequenceDecodeBHist (realNullSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realNullSequenceToEventFlow : RealNullSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealNullSequenceUp.mk S Z W R D L H C P N =>
      [realNullSequenceEncodeBHist S,
        realNullSequenceEncodeBHist Z,
        realNullSequenceEncodeBHist W,
        realNullSequenceEncodeBHist R,
        realNullSequenceEncodeBHist D,
        realNullSequenceEncodeBHist L,
        realNullSequenceEncodeBHist H,
        realNullSequenceEncodeBHist C,
        realNullSequenceEncodeBHist P,
        realNullSequenceEncodeBHist N]

private def realNullSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realNullSequenceEventAtDefault index rest

def realNullSequenceFromEventFlow
    (ef : EventFlow) : Option RealNullSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealNullSequenceUp.mk
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 0 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 1 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 2 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 3 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 4 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 5 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 6 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 7 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 8 ef))
      (realNullSequenceDecodeBHist (realNullSequenceEventAtDefault 9 ef)))

private theorem realNullSequence_round_trip :
    ∀ x : RealNullSequenceUp,
      realNullSequenceFromEventFlow (realNullSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Z W R D L H C P N =>
      change
        some
            (RealNullSequenceUp.mk
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist S))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist Z))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist W))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist R))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist D))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist L))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist H))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist C))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist P))
              (realNullSequenceDecodeBHist (realNullSequenceEncodeBHist N))) =
          some (RealNullSequenceUp.mk S Z W R D L H C P N)
      rw [realNullSequence_decode_encode_bhist S,
        realNullSequence_decode_encode_bhist Z,
        realNullSequence_decode_encode_bhist W,
        realNullSequence_decode_encode_bhist R,
        realNullSequence_decode_encode_bhist D,
        realNullSequence_decode_encode_bhist L,
        realNullSequence_decode_encode_bhist H,
        realNullSequence_decode_encode_bhist C,
        realNullSequence_decode_encode_bhist P,
        realNullSequence_decode_encode_bhist N]

private theorem realNullSequenceToEventFlow_injective
    {x y : RealNullSequenceUp} :
    realNullSequenceToEventFlow x = realNullSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realNullSequenceFromEventFlow (realNullSequenceToEventFlow x) =
        realNullSequenceFromEventFlow (realNullSequenceToEventFlow y) :=
    congrArg realNullSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realNullSequence_round_trip x).symm
      (Eq.trans hread (realNullSequence_round_trip y)))

def realNullSequenceFields : RealNullSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealNullSequenceUp.mk S Z W R D L H C P N => [S, Z, W, R, D, L, H, C, P, N]

private theorem realNullSequence_fields_faithful :
    ∀ x y : RealNullSequenceUp,
      realNullSequenceFields x = realNullSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S Z W R D L H C P N =>
      cases y with
      | mk S' Z' W' R' D' L' H' C' P' N' =>
          simp only [realNullSequenceFields] at h
          cases h
          rfl

instance realNullSequenceBHistCarrier : BHistCarrier RealNullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realNullSequenceToEventFlow
  fromEventFlow := realNullSequenceFromEventFlow

instance realNullSequenceChapterTasteGate : ChapterTasteGate RealNullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realNullSequenceFromEventFlow (realNullSequenceToEventFlow x) = some x
    exact realNullSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realNullSequenceToEventFlow_injective heq)

instance realNullSequenceFieldFaithful : FieldFaithful RealNullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realNullSequenceFields
  field_faithful := realNullSequence_fields_faithful

instance realNullSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealNullSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealNullSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealNullSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealNullSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realNullSequenceChapterTasteGate

theorem RealNullSequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealNullSequenceUp) ∧
      Nonempty (FieldFaithful RealNullSequenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealNullSequenceUp) ∧
          (∀ h : BHist,
            realNullSequenceDecodeBHist (realNullSequenceEncodeBHist h) = h) ∧
            (∀ x : RealNullSequenceUp,
              realNullSequenceFromEventFlow (realNullSequenceToEventFlow x) =
                some x) ∧
              (∀ x y : RealNullSequenceUp,
                realNullSequenceToEventFlow x = realNullSequenceToEventFlow y →
                  x = y) ∧
                realNullSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realNullSequenceChapterTasteGate⟩,
      ⟨realNullSequenceFieldFaithful⟩,
      ⟨realNullSequenceNontrivial⟩,
      realNullSequence_decode_encode_bhist,
      realNullSequence_round_trip,
      (fun _ _ heq => realNullSequenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealNullSequenceUp
