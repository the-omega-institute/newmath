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

private def bareObjectRefusalRawAt : Nat → EventFlow → RawEvent
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => bareObjectRefusalRawAt n rest

def bareObjectRefusalFromEventFlow : EventFlow → Option BareObjectRefusalUp
  | ef =>
      some
        (BareObjectRefusalUp.mk
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 0 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 1 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 2 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 3 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 4 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 5 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 6 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 7 ef))
          (bareObjectRefusalDecodeBHist (bareObjectRefusalRawAt 8 ef)))

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
          (∃ x y : BareObjectRefusalUp, x ≠ y) ∧
            (∀ x y : BareObjectRefusalUp, bareObjectRefusalFields x = bareObjectRefusalFields y →
              x = y) := by
  let decodeEncode :
      ∀ h : BHist, bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  let roundTrip :
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
        rw [decodeEncode objectName, decodeEncode missingFields, decodeEncode refusal,
          decodeEncode witnessAudit, decodeEncode ledger, decodeEncode transport,
          decodeEncode routes, decodeEncode provenance, decodeEncode localName]
  let flowInjective :
      ∀ x y : BareObjectRefusalUp,
        bareObjectRefusalToEventFlow x = bareObjectRefusalToEventFlow y → x = y := by
    intro x y heq
    have hread :
        bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow x) =
          bareObjectRefusalFromEventFlow (bareObjectRefusalToEventFlow y) :=
      congrArg bareObjectRefusalFromEventFlow heq
    exact Option.some.inj ((roundTrip x).symm.trans (hread.trans (roundTrip y)))
  let fieldFaithful :
      ∀ x y : BareObjectRefusalUp, bareObjectRefusalFields x = bareObjectRefusalFields y →
        x = y := by
    intro x y hfields
    cases x with
    | mk objectName missingFields refusal witnessAudit ledger transport routes provenance
        localName =>
        cases y with
        | mk objectName' missingFields' refusal' witnessAudit' ledger' transport' routes'
            provenance' localName' =>
            cases hfields
            rfl
  exact
    ⟨decodeEncode,
      roundTrip,
      flowInjective,
      ⟨BareObjectRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        BareObjectRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      fieldFaithful⟩

end BEDC.Derived.BareObjectRefusalUp
