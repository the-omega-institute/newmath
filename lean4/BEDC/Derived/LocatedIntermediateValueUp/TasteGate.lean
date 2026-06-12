import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntermediateValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntermediateValueUp : Type where
  | mk (E S B W R Q H C P N : BHist) : LocatedIntermediateValueUp
  deriving DecidableEq

def locatedIntermediateValueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntermediateValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntermediateValueEncodeBHist h

def locatedIntermediateValueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntermediateValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntermediateValueDecodeBHist tail)

private theorem LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntermediateValueFields : LocatedIntermediateValueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntermediateValueUp.mk E S B W R Q H C P N => [E, S, B, W, R, Q, H, C, P, N]

def locatedIntermediateValueToEventFlow : LocatedIntermediateValueUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntermediateValueFields x).map locatedIntermediateValueEncodeBHist

private def LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault index rest

def locatedIntermediateValueFromEventFlow (ef : EventFlow) : Option LocatedIntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntermediateValueUp.mk
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (locatedIntermediateValueDecodeBHist
        (LocatedIntermediateValueTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem LocatedIntermediateValueTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedIntermediateValueUp,
      locatedIntermediateValueFromEventFlow (locatedIntermediateValueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E S B W R Q H C P N =>
      change
        some
            (LocatedIntermediateValueUp.mk
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist E))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist S))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist B))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist W))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist R))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist Q))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist H))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist C))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist P))
              (locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist N))) =
          some (LocatedIntermediateValueUp.mk E S B W R Q H C P N)
      rw [LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode E,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode S,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode B,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode W,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode R,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode H,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode C,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode P,
        LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedIntermediateValueTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntermediateValueUp} :
    locatedIntermediateValueToEventFlow x = locatedIntermediateValueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntermediateValueFromEventFlow (locatedIntermediateValueToEventFlow x) =
        locatedIntermediateValueFromEventFlow (locatedIntermediateValueToEventFlow y) :=
    congrArg locatedIntermediateValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedIntermediateValueTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedIntermediateValueTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedIntermediateValueTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedIntermediateValueUp,
      locatedIntermediateValueFields x = locatedIntermediateValueFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 S1 B1 W1 R1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk E2 S2 B2 W2 R2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance LocatedIntermediateValueTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier LocatedIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntermediateValueToEventFlow
  fromEventFlow := locatedIntermediateValueFromEventFlow

instance LocatedIntermediateValueTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate LocatedIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedIntermediateValueFromEventFlow (locatedIntermediateValueToEventFlow x) = some x
    exact LocatedIntermediateValueTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedIntermediateValueTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance LocatedIntermediateValueTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful LocatedIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedIntermediateValueFields
  field_faithful := LocatedIntermediateValueTasteGate_single_carrier_alignment_fields_faithful

instance LocatedIntermediateValueTasteGate_single_carrier_alignment_Nontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedIntermediateValueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedIntermediateValueUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedIntermediateValueTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedIntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocatedIntermediateValueTasteGate_single_carrier_alignment_ChapterTasteGate

theorem LocatedIntermediateValueTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedIntermediateValueUp) ∧
      Nonempty (FieldFaithful LocatedIntermediateValueUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedIntermediateValueUp) ∧
          (∀ h : BHist,
            locatedIntermediateValueDecodeBHist (locatedIntermediateValueEncodeBHist h) = h) ∧
            (∀ x : LocatedIntermediateValueUp,
              locatedIntermediateValueFromEventFlow (locatedIntermediateValueToEventFlow x) =
                some x) ∧
              (∀ x y : LocatedIntermediateValueUp,
                locatedIntermediateValueToEventFlow x = locatedIntermediateValueToEventFlow y →
                  x = y) ∧
                locatedIntermediateValueEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨LocatedIntermediateValueTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      ⟨LocatedIntermediateValueTasteGate_single_carrier_alignment_FieldFaithful⟩,
      ⟨LocatedIntermediateValueTasteGate_single_carrier_alignment_Nontrivial⟩,
      LocatedIntermediateValueTasteGate_single_carrier_alignment_decode_encode,
      LocatedIntermediateValueTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact LocatedIntermediateValueTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedIntermediateValueUp
