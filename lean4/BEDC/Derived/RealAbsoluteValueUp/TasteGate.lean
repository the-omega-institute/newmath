import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealAbsoluteValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealAbsoluteValueUp : Type where
  | mk (S R delta D M E H C P N : BHist) : RealAbsoluteValueUp
  deriving DecidableEq

def realAbsoluteValueEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realAbsoluteValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realAbsoluteValueEncodeBHist h

def realAbsoluteValueDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realAbsoluteValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realAbsoluteValueDecodeBHist tail)

private theorem RealAbsoluteValueTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realAbsoluteValueFields : RealAbsoluteValueUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealAbsoluteValueUp.mk S R delta D M E H C P N => [S, R, delta, D, M, E, H, C, P, N]

def realAbsoluteValueToEventFlow : RealAbsoluteValueUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realAbsoluteValueFields x).map realAbsoluteValueEncodeBHist

private def realAbsoluteValueEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realAbsoluteValueEventAtDefault index rest

def realAbsoluteValueFromEventFlow : EventFlow -> Option RealAbsoluteValueUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealAbsoluteValueUp.mk
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 0 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 1 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 2 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 3 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 4 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 5 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 6 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 7 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 8 ef))
          (realAbsoluteValueDecodeBHist (realAbsoluteValueEventAtDefault 9 ef)))

private theorem RealAbsoluteValueTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealAbsoluteValueUp,
      realAbsoluteValueFromEventFlow (realAbsoluteValueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R delta D M E H C P N =>
      change
        some
          (RealAbsoluteValueUp.mk
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist S))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist R))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist delta))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist D))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist M))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist E))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist H))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist C))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist P))
            (realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist N))) =
          some (RealAbsoluteValueUp.mk S R delta D M E H C P N)
      rw [RealAbsoluteValueTasteGate_single_carrier_alignment_decode S,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode R,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode delta,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode D,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode M,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode E,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode H,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode C,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode P,
        RealAbsoluteValueTasteGate_single_carrier_alignment_decode N]

private theorem RealAbsoluteValueTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealAbsoluteValueUp} :
    realAbsoluteValueToEventFlow x = realAbsoluteValueToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realAbsoluteValueFromEventFlow (realAbsoluteValueToEventFlow x) =
        realAbsoluteValueFromEventFlow (realAbsoluteValueToEventFlow y) :=
    congrArg realAbsoluteValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealAbsoluteValueTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealAbsoluteValueTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealAbsoluteValueTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealAbsoluteValueUp, realAbsoluteValueFields x = realAbsoluteValueFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 delta1 D1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 delta2 D2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realAbsoluteValueBHistCarrier : BHistCarrier RealAbsoluteValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realAbsoluteValueToEventFlow
  fromEventFlow := realAbsoluteValueFromEventFlow

instance realAbsoluteValueFieldFaithful : FieldFaithful RealAbsoluteValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realAbsoluteValueFields
  field_faithful := RealAbsoluteValueTasteGate_single_carrier_alignment_fields

instance realAbsoluteValueChapterTasteGate : ChapterTasteGate RealAbsoluteValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realAbsoluteValueFromEventFlow (realAbsoluteValueToEventFlow x) = some x
    exact RealAbsoluteValueTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealAbsoluteValueTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realAbsoluteValueNontrivial : Nontrivial RealAbsoluteValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealAbsoluteValueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealAbsoluteValueUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealAbsoluteValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realAbsoluteValueChapterTasteGate

theorem RealAbsoluteValueTasteGate_single_carrier_alignment :
    (∀ h : BHist, realAbsoluteValueDecodeBHist (realAbsoluteValueEncodeBHist h) = h) ∧
      (∀ x : RealAbsoluteValueUp,
        realAbsoluteValueFromEventFlow (realAbsoluteValueToEventFlow x) = some x) ∧
        (∀ x y : RealAbsoluteValueUp,
          realAbsoluteValueToEventFlow x = realAbsoluteValueToEventFlow y -> x = y) ∧
          Nonempty (BHistCarrier RealAbsoluteValueUp) ∧
            Nonempty (FieldFaithful RealAbsoluteValueUp) ∧
              Nonempty (ChapterTasteGate RealAbsoluteValueUp) ∧
                realAbsoluteValueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨RealAbsoluteValueTasteGate_single_carrier_alignment_decode,
      RealAbsoluteValueTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealAbsoluteValueTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      ⟨realAbsoluteValueBHistCarrier⟩,
      ⟨realAbsoluteValueFieldFaithful⟩,
      ⟨realAbsoluteValueChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealAbsoluteValueUp
