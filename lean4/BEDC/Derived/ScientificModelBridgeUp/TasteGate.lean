import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScientificModelBridgeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScientificModelBridgeUp : Type where
  | mk :
      (object audit bridge modelAudit openFit ledger prediction transport hsameRow contRow
        provenance name : BHist) →
      ScientificModelBridgeUp
  deriving DecidableEq

def scientificModelBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scientificModelBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scientificModelBridgeEncodeBHist h

def scientificModelBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scientificModelBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scientificModelBridgeDecodeBHist tail)

private theorem scientificModelBridge_decode_encode_bhist :
    ∀ h : BHist, scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def scientificModelBridgeFields : ScientificModelBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScientificModelBridgeUp.mk object audit bridge modelAudit openFit ledger prediction
      transport hsameRow contRow provenance name =>
      [object, audit, bridge, modelAudit, openFit, ledger, prediction, transport,
        hsameRow, contRow, provenance, name]

def scientificModelBridgeToEventFlow : ScientificModelBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ScientificModelBridgeUp.mk object audit bridge modelAudit openFit ledger prediction
      transport hsameRow contRow provenance name =>
      [[BMark.b0],
        scientificModelBridgeEncodeBHist object,
        [BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist bridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist modelAudit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist openFit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist prediction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        scientificModelBridgeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist hsameRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist contRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificModelBridgeEncodeBHist name]

private def scientificModelBridgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => scientificModelBridgeEventAtDefault index rest

def scientificModelBridgeFromEventFlow (ef : EventFlow) : Option ScientificModelBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ScientificModelBridgeUp.mk
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 1 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 3 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 5 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 7 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 9 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 11 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 13 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 15 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 17 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 19 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 21 ef))
      (scientificModelBridgeDecodeBHist (scientificModelBridgeEventAtDefault 23 ef)))

private theorem scientificModelBridge_round_trip :
    ∀ x : ScientificModelBridgeUp,
      scientificModelBridgeFromEventFlow (scientificModelBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk object audit bridge modelAudit openFit ledger prediction transport hsameRow contRow
      provenance name =>
      change
        some
          (ScientificModelBridgeUp.mk
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist object))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist audit))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist bridge))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist modelAudit))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist openFit))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist ledger))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist prediction))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist transport))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist hsameRow))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist contRow))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist provenance))
            (scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist name))) =
          some
            (ScientificModelBridgeUp.mk object audit bridge modelAudit openFit ledger
              prediction transport hsameRow contRow provenance name)
      rw [scientificModelBridge_decode_encode_bhist object,
        scientificModelBridge_decode_encode_bhist audit,
        scientificModelBridge_decode_encode_bhist bridge,
        scientificModelBridge_decode_encode_bhist modelAudit,
        scientificModelBridge_decode_encode_bhist openFit,
        scientificModelBridge_decode_encode_bhist ledger,
        scientificModelBridge_decode_encode_bhist prediction,
        scientificModelBridge_decode_encode_bhist transport,
        scientificModelBridge_decode_encode_bhist hsameRow,
        scientificModelBridge_decode_encode_bhist contRow,
        scientificModelBridge_decode_encode_bhist provenance,
        scientificModelBridge_decode_encode_bhist name]

private theorem scientificModelBridgeToEventFlow_injective {x y : ScientificModelBridgeUp} :
    scientificModelBridgeToEventFlow x = scientificModelBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      scientificModelBridgeFromEventFlow (scientificModelBridgeToEventFlow x) =
        scientificModelBridgeFromEventFlow (scientificModelBridgeToEventFlow y) :=
    congrArg scientificModelBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (scientificModelBridge_round_trip x).symm
      (Eq.trans hread (scientificModelBridge_round_trip y)))

private theorem scientificModelBridge_field_faithful :
    ∀ x y : ScientificModelBridgeUp,
      scientificModelBridgeFields x = scientificModelBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk object₁ audit₁ bridge₁ modelAudit₁ openFit₁ ledger₁ prediction₁ transport₁
      hsameRow₁ contRow₁ provenance₁ name₁ =>
      cases y with
      | mk object₂ audit₂ bridge₂ modelAudit₂ openFit₂ ledger₂ prediction₂ transport₂
          hsameRow₂ contRow₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance scientificModelBridgeBHistCarrier : BHistCarrier ScientificModelBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scientificModelBridgeToEventFlow
  fromEventFlow := scientificModelBridgeFromEventFlow

instance scientificModelBridgeChapterTasteGate : ChapterTasteGate ScientificModelBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scientificModelBridgeFromEventFlow (scientificModelBridgeToEventFlow x) = some x
    exact scientificModelBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (scientificModelBridgeToEventFlow_injective heq)

instance scientificModelBridgeFieldFaithful : FieldFaithful ScientificModelBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := scientificModelBridgeFields
  field_faithful := scientificModelBridge_field_faithful

def taste_gate : ChapterTasteGate ScientificModelBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scientificModelBridgeChapterTasteGate

theorem ScientificModelBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, scientificModelBridgeDecodeBHist (scientificModelBridgeEncodeBHist h) = h) ∧
      (∀ x : ScientificModelBridgeUp,
        scientificModelBridgeFromEventFlow (scientificModelBridgeToEventFlow x) = some x) ∧
        (∀ x y : ScientificModelBridgeUp,
          scientificModelBridgeToEventFlow x = scientificModelBridgeToEventFlow y → x = y) ∧
          scientificModelBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact scientificModelBridge_decode_encode_bhist
  · constructor
    · exact scientificModelBridge_round_trip
    · constructor
      · intro x y heq
        exact scientificModelBridgeToEventFlow_injective heq
      · rfl

end BEDC.Derived.ScientificModelBridgeUp.TasteGate
