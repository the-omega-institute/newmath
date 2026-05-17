import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BareObjectRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BareObjectRefusalUp : Type where
  | mk :
      (objectName missingFields refusal witnessAudit ledger transport routes provenance
        localName : BHist) →
      BareObjectRefusalUp
  deriving DecidableEq

def bareObjectRefusalEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bareObjectRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bareObjectRefusalEncodeBHist h

def bareObjectRefusalDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bareObjectRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bareObjectRefusalDecodeBHist tail)

private theorem bareObjectRefusal_decode_encode_bhist :
    ∀ h : BHist, bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bareObjectRefusalFields : BareObjectRefusalUp → List BHist
  | BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit ledger transport
      routes provenance localName =>
      [objectName, missingFields, refusal, witnessAudit, ledger, transport, routes,
        provenance, localName]

def bareObjectRefusalToEventFlow : BareObjectRefusalUp → EventFlow
  | x => (bareObjectRefusalFields x).map bareObjectRefusalEncodeBHist

def bareObjectRefusalFromEventFlow : EventFlow → Option BareObjectRefusalUp
  | [objectName, missingFields, refusal, witnessAudit, ledger, transport, routes,
      provenance, localName] =>
      some
        (BareObjectRefusalUp.mk
          (bareObjectRefusalDecodeBHist objectName)
          (bareObjectRefusalDecodeBHist missingFields)
          (bareObjectRefusalDecodeBHist refusal)
          (bareObjectRefusalDecodeBHist witnessAudit)
          (bareObjectRefusalDecodeBHist ledger)
          (bareObjectRefusalDecodeBHist transport)
          (bareObjectRefusalDecodeBHist routes)
          (bareObjectRefusalDecodeBHist provenance)
          (bareObjectRefusalDecodeBHist localName))
  | _ => none

private theorem bareObjectRefusal_round_trip :
    ∀ x : BareObjectRefusalUp,
      bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow x) = some x := by
  intro x
  cases x with
  | mk objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName =>
      change
        some
          (BareObjectRefusalUp.mk
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist objectName))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist missingFields))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist refusal))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist witnessAudit))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist ledger))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist transport))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist routes))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist provenance))
            (bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist localName))) =
          some
            (BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit ledger
              transport routes provenance localName)
      rw [bareObjectRefusal_decode_encode_bhist objectName,
        bareObjectRefusal_decode_encode_bhist missingFields,
        bareObjectRefusal_decode_encode_bhist refusal,
        bareObjectRefusal_decode_encode_bhist witnessAudit,
        bareObjectRefusal_decode_encode_bhist ledger,
        bareObjectRefusal_decode_encode_bhist transport,
        bareObjectRefusal_decode_encode_bhist routes,
        bareObjectRefusal_decode_encode_bhist provenance,
        bareObjectRefusal_decode_encode_bhist localName]

private theorem bareObjectRefusalToEventFlow_injective {x y : BareObjectRefusalUp} :
    bareObjectRefusalToEventFlow x = bareObjectRefusalToEventFlow y → x = y := by
  intro heq
  have hread :
      bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow x) =
        bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow y) :=
    congrArg bareObjectRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bareObjectRefusal_round_trip x).symm
      (Eq.trans hread (bareObjectRefusal_round_trip y)))

private theorem bareObjectRefusal_field_faithful :
    ∀ x y : BareObjectRefusalUp,
      bareObjectRefusalFields x = bareObjectRefusalFields y → x = y := by
  intro x y hfields
  cases x with
  | mk objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName =>
      cases y with
      | mk objectName' missingFields' refusal' witnessAudit' ledger' transport' routes'
          provenance' localName' =>
          cases hfields
          rfl

instance bareObjectRefusalBHistCarrier : BHistCarrier BareObjectRefusalUp where
  toEventFlow := bareObjectRefusalToEventFlow
  fromEventFlow := bareObjectRefusalFromEventFlow

instance bareObjectRefusalChapterTasteGate : ChapterTasteGate BareObjectRefusalUp where
  round_trip := by
    intro x
    change bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow x) = some x
    exact bareObjectRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bareObjectRefusalToEventFlow_injective heq)

instance bareObjectRefusalFieldFaithful : FieldFaithful BareObjectRefusalUp where
  fields := bareObjectRefusalFields
  field_faithful := bareObjectRefusal_field_faithful

instance bareObjectRefusalNontrivial : Nontrivial BareObjectRefusalUp where
  witness_pair :=
    ⟨BareObjectRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BareObjectRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BareObjectRefusalUp :=
  bareObjectRefusalChapterTasteGate

theorem BareObjectRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist h) = h) ∧
      (∀ x : BareObjectRefusalUp,
        bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow x) = some x) ∧
        (∀ x y : BareObjectRefusalUp,
          bareObjectRefusalToEventFlow x = bareObjectRefusalToEventFlow y → x = y) ∧
          Nonempty (Nontrivial BareObjectRefusalUp) ∧
            Nonempty (FieldFaithful BareObjectRefusalUp) := by
  exact
    ⟨bareObjectRefusal_decode_encode_bhist,
      bareObjectRefusal_round_trip,
      (fun _ _ heq => bareObjectRefusalToEventFlow_injective heq),
      ⟨bareObjectRefusalNontrivial⟩,
      ⟨bareObjectRefusalFieldFaithful⟩⟩

end BEDC.Derived.BareObjectRefusalUp
