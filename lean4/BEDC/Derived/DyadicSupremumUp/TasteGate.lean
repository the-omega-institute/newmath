import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicSupremumUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicSupremumUp : Type where
  | mk : (bounded approximation window tolerance handoff realSeal transport replay provenance name :
      BHist) → DyadicSupremumUp
  deriving DecidableEq

def dyadicSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicSupremumEncodeBHist h

def dyadicSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicSupremumDecodeBHist tail)

private theorem dyadicSupremum_decode_encode_bhist :
    ∀ h : BHist, dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicSupremumFields : DyadicSupremumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicSupremumUp.mk bounded approximation window tolerance handoff realSeal transport replay
      provenance name =>
      [bounded, approximation, window, tolerance, handoff, realSeal, transport, replay,
        provenance, name]

def dyadicSupremumToEventFlow : DyadicSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicSupremumUp.mk bounded approximation window tolerance handoff realSeal transport replay
      provenance name =>
      [[BMark.b1, BMark.b0, BMark.b1],
        dyadicSupremumEncodeBHist bounded,
        dyadicSupremumEncodeBHist approximation,
        dyadicSupremumEncodeBHist window,
        dyadicSupremumEncodeBHist tolerance,
        dyadicSupremumEncodeBHist handoff,
        dyadicSupremumEncodeBHist realSeal,
        dyadicSupremumEncodeBHist transport,
        dyadicSupremumEncodeBHist replay,
        dyadicSupremumEncodeBHist provenance,
        dyadicSupremumEncodeBHist name]

private def dyadicSupremumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicSupremumEventAt index rest

def dyadicSupremumFromEventFlow : EventFlow → Option DyadicSupremumUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DyadicSupremumUp.mk
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 1 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 2 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 3 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 4 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 5 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 6 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 7 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 8 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 9 ef))
          (dyadicSupremumDecodeBHist (dyadicSupremumEventAt 10 ef)))

private theorem dyadicSupremum_round_trip :
    ∀ x : DyadicSupremumUp,
      dyadicSupremumFromEventFlow (dyadicSupremumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bounded approximation window tolerance handoff realSeal transport replay provenance name =>
      change
        some
          (DyadicSupremumUp.mk
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist bounded))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist approximation))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist window))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist tolerance))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist handoff))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist realSeal))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist transport))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist replay))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist provenance))
            (dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist name))) =
          some
            (DyadicSupremumUp.mk bounded approximation window tolerance handoff realSeal transport
              replay provenance name)
      rw [dyadicSupremum_decode_encode_bhist bounded,
        dyadicSupremum_decode_encode_bhist approximation,
        dyadicSupremum_decode_encode_bhist window,
        dyadicSupremum_decode_encode_bhist tolerance,
        dyadicSupremum_decode_encode_bhist handoff,
        dyadicSupremum_decode_encode_bhist realSeal,
        dyadicSupremum_decode_encode_bhist transport,
        dyadicSupremum_decode_encode_bhist replay,
        dyadicSupremum_decode_encode_bhist provenance,
        dyadicSupremum_decode_encode_bhist name]

private theorem dyadicSupremumToEventFlow_injective {x y : DyadicSupremumUp} :
    dyadicSupremumToEventFlow x = dyadicSupremumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicSupremumFromEventFlow (dyadicSupremumToEventFlow x) =
        dyadicSupremumFromEventFlow (dyadicSupremumToEventFlow y) :=
    congrArg dyadicSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicSupremum_round_trip x).symm
      (Eq.trans hread (dyadicSupremum_round_trip y)))

private theorem dyadicSupremum_field_faithful :
    ∀ x y : DyadicSupremumUp, dyadicSupremumFields x = dyadicSupremumFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk bounded₁ approximation₁ window₁ tolerance₁ handoff₁ realSeal₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk bounded₂ approximation₂ window₂ tolerance₂ handoff₂ realSeal₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases h
          rfl

instance dyadicSupremumBHistCarrier : BHistCarrier DyadicSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicSupremumToEventFlow
  fromEventFlow := dyadicSupremumFromEventFlow

instance dyadicSupremumChapterTasteGate : ChapterTasteGate DyadicSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicSupremumFromEventFlow (dyadicSupremumToEventFlow x) = some x
    exact dyadicSupremum_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicSupremumToEventFlow_injective heq)

instance dyadicSupremumFieldFaithful : FieldFaithful DyadicSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicSupremumFields
  field_faithful := dyadicSupremum_field_faithful

instance dyadicSupremumNontrivial : Nontrivial DyadicSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicSupremumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicSupremumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicSupremumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicSupremumChapterTasteGate

theorem DyadicSupremumTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicSupremumUp) ∧
      Nonempty (FieldFaithful DyadicSupremumUp) ∧
      Nonempty (Nontrivial DyadicSupremumUp) ∧
      (∀ h : BHist, dyadicSupremumDecodeBHist (dyadicSupremumEncodeBHist h) = h) ∧
      (∀ x : DyadicSupremumUp,
        dyadicSupremumFromEventFlow (dyadicSupremumToEventFlow x) = some x) ∧
      (∀ x y : DyadicSupremumUp,
        dyadicSupremumToEventFlow x = dyadicSupremumToEventFlow y → x = y) ∧
      dyadicSupremumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨dyadicSupremumChapterTasteGate⟩
  · constructor
    · exact ⟨dyadicSupremumFieldFaithful⟩
    · constructor
      · exact ⟨dyadicSupremumNontrivial⟩
      · constructor
        · exact dyadicSupremum_decode_encode_bhist
        · constructor
          · exact dyadicSupremum_round_trip
          · constructor
            · intro x y heq
              exact dyadicSupremumToEventFlow_injective heq
            · rfl

end BEDC.Derived.DyadicSupremumUp.TasteGate
