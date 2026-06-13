import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TriggerBlockerDualityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TriggerBlockerDualityUp : Type where
  | mk (source algebra lattice blocker intersections nerve transport replay provenance localName :
      BHist) : TriggerBlockerDualityUp
  deriving DecidableEq

def triggerBlockerDualityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: triggerBlockerDualityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: triggerBlockerDualityEncodeBHist h

def triggerBlockerDualityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (triggerBlockerDualityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (triggerBlockerDualityDecodeBHist tail)

private theorem TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def triggerBlockerDualityFields : TriggerBlockerDualityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TriggerBlockerDualityUp.mk source algebra lattice blocker intersections nerve transport replay
      provenance localName =>
      [source, algebra, lattice, blocker, intersections, nerve, transport, replay, provenance,
        localName]

def triggerBlockerDualityToEventFlow : TriggerBlockerDualityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (triggerBlockerDualityFields x).map triggerBlockerDualityEncodeBHist

private def triggerBlockerDualityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => triggerBlockerDualityEventAtDefault index rest

def triggerBlockerDualityFromEventFlow
    (ef : EventFlow) : Option TriggerBlockerDualityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TriggerBlockerDualityUp.mk
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 0 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 1 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 2 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 3 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 4 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 5 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 6 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 7 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 8 ef))
      (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEventAtDefault 9 ef)))

private theorem TriggerBlockerDualityTasteGate_single_carrier_alignment_round_trip
    (x : TriggerBlockerDualityUp) :
    triggerBlockerDualityFromEventFlow (triggerBlockerDualityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source algebra lattice blocker intersections nerve transport replay provenance localName =>
      change
        some
          (TriggerBlockerDualityUp.mk
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist source))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist algebra))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist lattice))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist blocker))
            (triggerBlockerDualityDecodeBHist
              (triggerBlockerDualityEncodeBHist intersections))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist nerve))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist transport))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist replay))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist provenance))
            (triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist localName))) =
          some
            (TriggerBlockerDualityUp.mk source algebra lattice blocker intersections nerve
              transport replay provenance localName)
      rw [
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode source,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode algebra,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode lattice,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode blocker,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode intersections,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode nerve,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode transport,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode replay,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode provenance,
        TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode localName]

private theorem TriggerBlockerDualityTasteGate_single_carrier_alignment_injective
    {x y : TriggerBlockerDualityUp} :
    triggerBlockerDualityToEventFlow x = triggerBlockerDualityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      triggerBlockerDualityFromEventFlow (triggerBlockerDualityToEventFlow x) =
        triggerBlockerDualityFromEventFlow (triggerBlockerDualityToEventFlow y) :=
    congrArg triggerBlockerDualityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TriggerBlockerDualityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TriggerBlockerDualityTasteGate_single_carrier_alignment_round_trip y)))

private theorem TriggerBlockerDualityTasteGate_single_carrier_alignment_fields :
    ∀ x y : TriggerBlockerDualityUp,
      triggerBlockerDualityFields x = triggerBlockerDualityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ algebra₁ lattice₁ blocker₁ intersections₁ nerve₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk source₂ algebra₂ lattice₂ blocker₂ intersections₂ nerve₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance triggerBlockerDualityBHistCarrier : BHistCarrier TriggerBlockerDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := triggerBlockerDualityToEventFlow
  fromEventFlow := triggerBlockerDualityFromEventFlow

instance triggerBlockerDualityChapterTasteGate : ChapterTasteGate TriggerBlockerDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change triggerBlockerDualityFromEventFlow (triggerBlockerDualityToEventFlow x) = some x
    exact TriggerBlockerDualityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TriggerBlockerDualityTasteGate_single_carrier_alignment_injective heq)

instance triggerBlockerDualityFieldFaithful : FieldFaithful TriggerBlockerDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := triggerBlockerDualityFields
  field_faithful := TriggerBlockerDualityTasteGate_single_carrier_alignment_fields

instance triggerBlockerDualityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial TriggerBlockerDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TriggerBlockerDualityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TriggerBlockerDualityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TriggerBlockerDualityTasteGate_single_carrier_alignment :
    (∀ h : BHist, triggerBlockerDualityDecodeBHist (triggerBlockerDualityEncodeBHist h) = h) ∧
      (∀ x : TriggerBlockerDualityUp,
        triggerBlockerDualityFromEventFlow (triggerBlockerDualityToEventFlow x) = some x) ∧
        (∀ x y : TriggerBlockerDualityUp,
          triggerBlockerDualityToEventFlow x = triggerBlockerDualityToEventFlow y → x = y) ∧
          triggerBlockerDualityEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : TriggerBlockerDualityUp,
              triggerBlockerDualityFields x = triggerBlockerDualityFields y → x = y) ∧
              (∃ x y : TriggerBlockerDualityUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TriggerBlockerDualityTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact TriggerBlockerDualityTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact TriggerBlockerDualityTasteGate_single_carrier_alignment_injective heq
      · constructor
        · rfl
        · constructor
          · exact TriggerBlockerDualityTasteGate_single_carrier_alignment_fields
          · exact
              ⟨TriggerBlockerDualityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                TriggerBlockerDualityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.TriggerBlockerDualityUp
