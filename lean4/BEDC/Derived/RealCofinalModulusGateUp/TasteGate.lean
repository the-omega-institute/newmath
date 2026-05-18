import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCofinalModulusGateUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCofinalModulusGateUp : Type where
  | mk :
      (tailSchedule modulusComparison window witness realSeal exactness transport replay
        provenance name : BHist) →
      RealCofinalModulusGateUp
  deriving DecidableEq

def realCofinalModulusGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCofinalModulusGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCofinalModulusGateEncodeBHist h

def realCofinalModulusGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCofinalModulusGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCofinalModulusGateDecodeBHist tail)

private theorem realCofinalModulusGate_decode_encode_bhist :
    ∀ h : BHist,
      realCofinalModulusGateDecodeBHist (realCofinalModulusGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCofinalModulusGateFields : RealCofinalModulusGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCofinalModulusGateUp.mk tailSchedule modulusComparison window witness realSeal
      exactness transport replay provenance name =>
      [tailSchedule, modulusComparison, window, witness, realSeal, exactness, transport,
        replay, provenance, name]

def realCofinalModulusGateToEventFlow : RealCofinalModulusGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCofinalModulusGateFields x).map realCofinalModulusGateEncodeBHist

private def realCofinalModulusGateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCofinalModulusGateEventAtDefault index rest

def realCofinalModulusGateFromEventFlow
    (ef : EventFlow) : Option RealCofinalModulusGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCofinalModulusGateUp.mk
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 0 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 1 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 2 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 3 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 4 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 5 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 6 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 7 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 8 ef))
      (realCofinalModulusGateDecodeBHist (realCofinalModulusGateEventAtDefault 9 ef)))

private theorem realCofinalModulusGate_round_trip :
    ∀ x : RealCofinalModulusGateUp,
      realCofinalModulusGateFromEventFlow
        (realCofinalModulusGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tailSchedule modulusComparison window witness realSeal exactness transport replay
      provenance name =>
      change
        some
          (RealCofinalModulusGateUp.mk
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist tailSchedule))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist modulusComparison))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist window))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist witness))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist realSeal))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist exactness))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist transport))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist replay))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist provenance))
            (realCofinalModulusGateDecodeBHist
              (realCofinalModulusGateEncodeBHist name))) =
          some
            (RealCofinalModulusGateUp.mk tailSchedule modulusComparison window witness
              realSeal exactness transport replay provenance name)
      rw [realCofinalModulusGate_decode_encode_bhist tailSchedule,
        realCofinalModulusGate_decode_encode_bhist modulusComparison,
        realCofinalModulusGate_decode_encode_bhist window,
        realCofinalModulusGate_decode_encode_bhist witness,
        realCofinalModulusGate_decode_encode_bhist realSeal,
        realCofinalModulusGate_decode_encode_bhist exactness,
        realCofinalModulusGate_decode_encode_bhist transport,
        realCofinalModulusGate_decode_encode_bhist replay,
        realCofinalModulusGate_decode_encode_bhist provenance,
        realCofinalModulusGate_decode_encode_bhist name]

private theorem realCofinalModulusGateToEventFlow_injective
    {x y : RealCofinalModulusGateUp} :
    realCofinalModulusGateToEventFlow x = realCofinalModulusGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCofinalModulusGateFromEventFlow (realCofinalModulusGateToEventFlow x) =
        realCofinalModulusGateFromEventFlow (realCofinalModulusGateToEventFlow y) :=
    congrArg realCofinalModulusGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCofinalModulusGate_round_trip x).symm
      (Eq.trans hread (realCofinalModulusGate_round_trip y)))

private theorem realCofinalModulusGate_fields_faithful :
    ∀ x y : RealCofinalModulusGateUp,
      realCofinalModulusGateFields x = realCofinalModulusGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk t₁ m₁ w₁ s₁ r₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk t₂ m₂ w₂ s₂ r₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance realCofinalModulusGateBHistCarrier : BHistCarrier RealCofinalModulusGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCofinalModulusGateToEventFlow
  fromEventFlow := realCofinalModulusGateFromEventFlow

instance realCofinalModulusGateChapterTasteGate :
    ChapterTasteGate RealCofinalModulusGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCofinalModulusGateFromEventFlow (realCofinalModulusGateToEventFlow x) = some x
    exact realCofinalModulusGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCofinalModulusGateToEventFlow_injective heq)

instance realCofinalModulusGateFieldFaithful : FieldFaithful RealCofinalModulusGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCofinalModulusGateFields
  field_faithful := realCofinalModulusGate_fields_faithful

instance realCofinalModulusGateNontrivial : Nontrivial RealCofinalModulusGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCofinalModulusGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCofinalModulusGateUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCofinalModulusGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCofinalModulusGateChapterTasteGate

def taste_gate_witness : FieldFaithful RealCofinalModulusGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCofinalModulusGateFieldFaithful

theorem RealCofinalModulusGateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCofinalModulusGateDecodeBHist (realCofinalModulusGateEncodeBHist h) = h) ∧
      (∀ x : RealCofinalModulusGateUp,
        realCofinalModulusGateFromEventFlow
          (realCofinalModulusGateToEventFlow x) = some x) ∧
        Nonempty (ChapterTasteGate RealCofinalModulusGateUp) ∧
          realCofinalModulusGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨realCofinalModulusGate_decode_encode_bhist,
      realCofinalModulusGate_round_trip,
      ⟨realCofinalModulusGateChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealCofinalModulusGateUp.TasteGate
