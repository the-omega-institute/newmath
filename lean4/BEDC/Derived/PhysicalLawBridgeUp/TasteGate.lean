import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalLawBridgeUp : Type where
  | mk :
      (law empirical bridge object fit failure transport replay provenance name : BHist) →
        PhysicalLawBridgeUp
  deriving DecidableEq

def physicalLawBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalLawBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalLawBridgeEncodeBHist h

def physicalLawBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalLawBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalLawBridgeDecodeBHist tail)

private theorem physicalLawBridgeDecode_encode_bhist :
    ∀ h : BHist,
      physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def physicalLawBridgeToEventFlow : PhysicalLawBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalLawBridgeUp.mk law empirical bridge object fit failure transport replay provenance
      name =>
      [[BMark.b0],
        physicalLawBridgeEncodeBHist law,
        [BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist empirical,
        [BMark.b1, BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist bridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist object,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist fit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicalLawBridgeEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        physicalLawBridgeEncodeBHist name]

private def physicalLawBridgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      physicalLawBridgeEventAtDefault index rest

def physicalLawBridgeFromEventFlow (ef : EventFlow) : Option PhysicalLawBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhysicalLawBridgeUp.mk
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 1 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 3 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 5 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 7 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 9 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 11 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 13 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 15 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 17 ef))
      (physicalLawBridgeDecodeBHist (physicalLawBridgeEventAtDefault 19 ef)))

private theorem physicalLawBridge_round_trip :
    ∀ x : PhysicalLawBridgeUp,
      physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk law empirical bridge object fit failure transport replay provenance name =>
      change
        some
          (PhysicalLawBridgeUp.mk
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist law))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist empirical))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist bridge))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist object))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist fit))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist failure))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist transport))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist replay))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist provenance))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist name))) =
          some
            (PhysicalLawBridgeUp.mk law empirical bridge object fit failure transport replay
              provenance name)
      rw [physicalLawBridgeDecode_encode_bhist law,
        physicalLawBridgeDecode_encode_bhist empirical,
        physicalLawBridgeDecode_encode_bhist bridge,
        physicalLawBridgeDecode_encode_bhist object,
        physicalLawBridgeDecode_encode_bhist fit,
        physicalLawBridgeDecode_encode_bhist failure,
        physicalLawBridgeDecode_encode_bhist transport,
        physicalLawBridgeDecode_encode_bhist replay,
        physicalLawBridgeDecode_encode_bhist provenance,
        physicalLawBridgeDecode_encode_bhist name]

private theorem physicalLawBridgeToEventFlow_injective {x y : PhysicalLawBridgeUp} :
    physicalLawBridgeToEventFlow x = physicalLawBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) =
        physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow y) :=
    congrArg physicalLawBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalLawBridge_round_trip x).symm
      (Eq.trans hread (physicalLawBridge_round_trip y)))

private def physicalLawBridgeFields : PhysicalLawBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalLawBridgeUp.mk law empirical bridge object fit failure transport replay provenance
      name =>
      [law, empirical, bridge, object, fit, failure, transport, replay, provenance, name]

private theorem physicalLawBridge_field_faithful :
    ∀ x y : PhysicalLawBridgeUp,
      physicalLawBridgeFields x = physicalLawBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk law empirical bridge object fit failure transport replay provenance name =>
      cases y with
      | mk law' empirical' bridge' object' fit' failure' transport' replay' provenance'
          name' =>
          cases hfields
          rfl

instance physicalLawBridgeBHistCarrier : BHistCarrier PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalLawBridgeToEventFlow
  fromEventFlow := physicalLawBridgeFromEventFlow

instance physicalLawBridgeChapterTasteGate : ChapterTasteGate PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := physicalLawBridge_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalLawBridgeToEventFlow_injective heq)

instance physicalLawBridgeFieldFaithful : FieldFaithful PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalLawBridgeFields
  field_faithful := physicalLawBridge_field_faithful

instance physicalLawBridgeNontrivial : Nontrivial PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalLawBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalLawBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalLawBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalLawBridgeChapterTasteGate

theorem PhysicalLawBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist h) = h) ∧
      (∀ x : PhysicalLawBridgeUp,
        physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x) ∧
        (∀ x y : PhysicalLawBridgeUp,
          physicalLawBridgeToEventFlow x = physicalLawBridgeToEventFlow y → x = y) ∧
          physicalLawBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact physicalLawBridgeDecode_encode_bhist
  · constructor
    · exact physicalLawBridge_round_trip
    · constructor
      · intro x y heq
        exact physicalLawBridgeToEventFlow_injective heq
      · rfl

end BEDC.Derived.PhysicalLawBridgeUp
