import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntermediateValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntermediateValueUp : Type where
  | mk (I S B Q W R E H C P N : BHist) : DyadicIntermediateValueUp
  deriving DecidableEq

def dyadicIntermediateValueEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntermediateValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntermediateValueEncodeBHist h

def dyadicIntermediateValueDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntermediateValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntermediateValueDecodeBHist tail)

private theorem DyadicIntermediateValueTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntermediateValueFields : DyadicIntermediateValueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntermediateValueUp.mk I S B Q W R E H C P N => [I, S, B, Q, W, R, E, H, C, P, N]

def dyadicIntermediateValueToEventFlow : DyadicIntermediateValueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntermediateValueFields x).map dyadicIntermediateValueEncodeBHist

private def dyadicIntermediateValueEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntermediateValueEventAtDefault index rest

def dyadicIntermediateValueFromEventFlow (ef : EventFlow) : Option DyadicIntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntermediateValueUp.mk
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 0 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 1 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 2 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 3 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 4 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 5 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 6 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 7 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 8 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 9 ef))
      (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEventAtDefault 10 ef)))

private theorem DyadicIntermediateValueTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicIntermediateValueUp,
      dyadicIntermediateValueFromEventFlow (dyadicIntermediateValueToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S B Q W R E H C P N =>
      change
        some
          (DyadicIntermediateValueUp.mk
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist I))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist S))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist B))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist Q))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist W))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist R))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist E))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist H))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist C))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist P))
            (dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist N))) =
          some (DyadicIntermediateValueUp.mk I S B Q W R E H C P N)
      rw [DyadicIntermediateValueTasteGate_single_carrier_alignment_decode I,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode S,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode B,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode Q,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode W,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode R,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode E,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode H,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode C,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode P,
        DyadicIntermediateValueTasteGate_single_carrier_alignment_decode N]

private theorem DyadicIntermediateValueTasteGate_single_carrier_alignment_injective
    {x y : DyadicIntermediateValueUp} :
    dyadicIntermediateValueToEventFlow x = dyadicIntermediateValueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntermediateValueFromEventFlow (dyadicIntermediateValueToEventFlow x) =
        dyadicIntermediateValueFromEventFlow (dyadicIntermediateValueToEventFlow y) :=
    congrArg dyadicIntermediateValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntermediateValueTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicIntermediateValueTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicIntermediateValueTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicIntermediateValueUp,
      dyadicIntermediateValueFields x = dyadicIntermediateValueFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 S1 B1 Q1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 S2 B2 Q2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicIntermediateValueBHistCarrier : BHistCarrier DyadicIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntermediateValueToEventFlow
  fromEventFlow := dyadicIntermediateValueFromEventFlow

instance dyadicIntermediateValueChapterTasteGate :
    ChapterTasteGate DyadicIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntermediateValueFromEventFlow (dyadicIntermediateValueToEventFlow x) = some x
    exact DyadicIntermediateValueTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntermediateValueTasteGate_single_carrier_alignment_injective heq)

instance dyadicIntermediateValueFieldFaithful : FieldFaithful DyadicIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntermediateValueFields
  field_faithful := DyadicIntermediateValueTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate DyadicIntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntermediateValueChapterTasteGate

def taste_gate_witness : FieldFaithful DyadicIntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntermediateValueFieldFaithful

theorem DyadicIntermediateValueTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicIntermediateValueDecodeBHist (dyadicIntermediateValueEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicIntermediateValueUp) ∧
        Nonempty (ChapterTasteGate DyadicIntermediateValueUp) ∧
          dyadicIntermediateValueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · exact ⟨dyadicIntermediateValueBHistCarrier⟩
  constructor
  · exact ⟨dyadicIntermediateValueChapterTasteGate⟩
  · rfl

end BEDC.Derived.DyadicIntermediateValueUp
