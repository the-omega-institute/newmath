import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CircleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CircleUp : Type where
  | mk (B R M K S H P N : BHist) : CircleUp
  deriving DecidableEq

def CircleTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CircleTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CircleTasteGate_single_carrier_alignment_encodeBHist h

def CircleTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CircleTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CircleTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CircleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CircleTasteGate_single_carrier_alignment_fields : CircleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CircleUp.mk B R M K S H P N => [B, R, M, K, S, H, P, N]

def CircleTasteGate_single_carrier_alignment_toEventFlow :
    CircleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CircleTasteGate_single_carrier_alignment_fields x).map
        CircleTasteGate_single_carrier_alignment_encodeBHist

private def CircleTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CircleTasteGate_single_carrier_alignment_eventAtDefault index rest

def CircleTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CircleUp.mk
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (CircleTasteGate_single_carrier_alignment_decodeBHist
        (CircleTasteGate_single_carrier_alignment_eventAtDefault 7 ef)))

private theorem CircleTasteGate_single_carrier_alignment_round_trip
    (x : CircleUp) :
    CircleTasteGate_single_carrier_alignment_fromEventFlow
      (CircleTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B R M K S H P N =>
      change
        some
          (CircleUp.mk
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist B))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist R))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist M))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist K))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist S))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist H))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist P))
            (CircleTasteGate_single_carrier_alignment_decodeBHist
              (CircleTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CircleUp.mk B R M K S H P N)
      rw [CircleTasteGate_single_carrier_alignment_decode_encode B,
        CircleTasteGate_single_carrier_alignment_decode_encode R,
        CircleTasteGate_single_carrier_alignment_decode_encode M,
        CircleTasteGate_single_carrier_alignment_decode_encode K,
        CircleTasteGate_single_carrier_alignment_decode_encode S,
        CircleTasteGate_single_carrier_alignment_decode_encode H,
        CircleTasteGate_single_carrier_alignment_decode_encode P,
        CircleTasteGate_single_carrier_alignment_decode_encode N]

private theorem CircleTasteGate_single_carrier_alignment_injective
    {x y : CircleUp} :
    CircleTasteGate_single_carrier_alignment_toEventFlow x =
      CircleTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CircleTasteGate_single_carrier_alignment_fromEventFlow
          (CircleTasteGate_single_carrier_alignment_toEventFlow x) =
        CircleTasteGate_single_carrier_alignment_fromEventFlow
          (CircleTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CircleTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CircleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CircleTasteGate_single_carrier_alignment_round_trip y)))

private theorem CircleTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CircleUp,
      CircleTasteGate_single_carrier_alignment_fields x =
        CircleTasteGate_single_carrier_alignment_fields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ R₁ M₁ K₁ S₁ H₁ P₁ N₁ =>
      cases y with
      | mk B₂ R₂ M₂ K₂ S₂ H₂ P₂ N₂ =>
          cases hfields
          rfl

instance CircleTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CircleTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CircleTasteGate_single_carrier_alignment_fromEventFlow

instance CircleTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CircleTasteGate_single_carrier_alignment_fields
  field_faithful := CircleTasteGate_single_carrier_alignment_field_faithful

instance CircleTasteGate_single_carrier_alignment_Nontrivial :
    BEDC.Meta.TasteGate.Nontrivial CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CircleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CircleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CircleTasteGate_single_carrier_alignment :
    ChapterTasteGate CircleUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      CircleTasteGate_single_carrier_alignment_fromEventFlow
        (CircleTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CircleTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (CircleTasteGate_single_carrier_alignment_injective heq)

instance CircleTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CircleTasteGate_single_carrier_alignment

def CircleTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CircleTasteGate_single_carrier_alignment

end BEDC.Derived.CircleUp
