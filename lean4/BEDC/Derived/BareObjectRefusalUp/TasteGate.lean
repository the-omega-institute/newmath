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
      let objectNameRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist objectName)
      let missingFieldsRead :=
        bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist missingFields)
      let refusalRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist refusal)
      let witnessAuditRead :=
        bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist witnessAudit)
      let ledgerRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist ledger)
      let transportRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist transport)
      let routesRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist routes)
      let provenanceRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist provenance)
      let localNameRead := bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist localName)
      have hObject : objectNameRead = objectName :=
        bareObjectRefusal_decode_encode_bhist objectName
      have hMissing : missingFieldsRead = missingFields :=
        bareObjectRefusal_decode_encode_bhist missingFields
      have hRefusal : refusalRead = refusal :=
        bareObjectRefusal_decode_encode_bhist refusal
      have hWitness : witnessAuditRead = witnessAudit :=
        bareObjectRefusal_decode_encode_bhist witnessAudit
      have hLedger : ledgerRead = ledger :=
        bareObjectRefusal_decode_encode_bhist ledger
      have hTransport : transportRead = transport :=
        bareObjectRefusal_decode_encode_bhist transport
      have hRoutes : routesRead = routes :=
        bareObjectRefusal_decode_encode_bhist routes
      have hProvenance : provenanceRead = provenance :=
        bareObjectRefusal_decode_encode_bhist provenance
      have hLocal : localNameRead = localName :=
        bareObjectRefusal_decode_encode_bhist localName
      have hCarrier :
          BareObjectRefusalUp.mk objectNameRead missingFieldsRead refusalRead witnessAuditRead
              ledgerRead transportRead routesRead provenanceRead localNameRead =
            BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit ledger transport
              routes provenance localName := by
        exact
          Eq.trans
            (congrArg
              (fun z =>
                BareObjectRefusalUp.mk z missingFieldsRead refusalRead witnessAuditRead
                  ledgerRead transportRead routesRead provenanceRead localNameRead)
              hObject)
            (Eq.trans
              (congrArg
                (fun z =>
                  BareObjectRefusalUp.mk objectName z refusalRead witnessAuditRead ledgerRead
                    transportRead routesRead provenanceRead localNameRead)
                hMissing)
              (Eq.trans
                (congrArg
                  (fun z =>
                    BareObjectRefusalUp.mk objectName missingFields z witnessAuditRead ledgerRead
                      transportRead routesRead provenanceRead localNameRead)
                  hRefusal)
                (Eq.trans
                  (congrArg
                    (fun z =>
                      BareObjectRefusalUp.mk objectName missingFields refusal z ledgerRead
                        transportRead routesRead provenanceRead localNameRead)
                    hWitness)
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit z
                          transportRead routesRead provenanceRead localNameRead)
                      hLedger)
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit
                            ledger z routesRead provenanceRead localNameRead)
                        hTransport)
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit
                              ledger transport z provenanceRead localNameRead)
                          hRoutes)
                        (Eq.trans
                          (congrArg
                            (fun z =>
                              BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit
                                ledger transport routes z localNameRead)
                            hProvenance)
                          (congrArg
                            (fun z =>
                              BareObjectRefusalUp.mk objectName missingFields refusal witnessAudit
                                ledger transport routes provenance z)
                            hLocal))))))))
      exact congrArg Option.some hCarrier

private theorem bareObjectRefusalToEventFlow_injective {x y : BareObjectRefusalUp} :
    bareObjectRefusalToEventFlow x = bareObjectRefusalToEventFlow y → x = y := by
  intro heq
  cases x with
  | mk objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName =>
      cases y with
      | mk objectName' missingFields' refusal' witnessAudit' ledger' transport' routes'
          provenance' localName' =>
          change
            [bareObjectRefusalEncodeBHist objectName,
              bareObjectRefusalEncodeBHist missingFields,
              bareObjectRefusalEncodeBHist refusal,
              bareObjectRefusalEncodeBHist witnessAudit,
              bareObjectRefusalEncodeBHist ledger,
              bareObjectRefusalEncodeBHist transport,
              bareObjectRefusalEncodeBHist routes,
              bareObjectRefusalEncodeBHist provenance,
              bareObjectRefusalEncodeBHist localName] =
            [bareObjectRefusalEncodeBHist objectName',
              bareObjectRefusalEncodeBHist missingFields',
              bareObjectRefusalEncodeBHist refusal',
              bareObjectRefusalEncodeBHist witnessAudit',
              bareObjectRefusalEncodeBHist ledger',
              bareObjectRefusalEncodeBHist transport',
              bareObjectRefusalEncodeBHist routes',
              bareObjectRefusalEncodeBHist provenance',
              bareObjectRefusalEncodeBHist localName'] at heq
          injection heq with hObject t1
          injection t1 with hMissing t2
          injection t2 with hRefusal t3
          injection t3 with hWitness t4
          injection t4 with hLedger t5
          injection t5 with hTransport t6
          injection t6 with hRoutes t7
          injection t7 with hProvenance t8
          injection t8 with hLocal _
          have objectSame : objectName = objectName' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist objectName).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hObject)
                (bareObjectRefusal_decode_encode_bhist objectName'))
          have missingSame : missingFields = missingFields' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist missingFields).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hMissing)
                (bareObjectRefusal_decode_encode_bhist missingFields'))
          have refusalSame : refusal = refusal' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist refusal).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hRefusal)
                (bareObjectRefusal_decode_encode_bhist refusal'))
          have witnessSame : witnessAudit = witnessAudit' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist witnessAudit).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hWitness)
                (bareObjectRefusal_decode_encode_bhist witnessAudit'))
          have ledgerSame : ledger = ledger' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist ledger).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hLedger)
                (bareObjectRefusal_decode_encode_bhist ledger'))
          have transportSame : transport = transport' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist transport).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hTransport)
                (bareObjectRefusal_decode_encode_bhist transport'))
          have routesSame : routes = routes' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist routes).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hRoutes)
                (bareObjectRefusal_decode_encode_bhist routes'))
          have provenanceSame : provenance = provenance' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist provenance).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hProvenance)
                (bareObjectRefusal_decode_encode_bhist provenance'))
          have localSame : localName = localName' := by
            exact Eq.trans (bareObjectRefusal_decode_encode_bhist localName).symm
              (Eq.trans (congrArg bareObjectRefusalDecodeBHist hLocal)
                (bareObjectRefusal_decode_encode_bhist localName'))
          cases objectSame
          cases missingSame
          cases refusalSame
          cases witnessSame
          cases ledgerSame
          cases transportSame
          cases routesSame
          cases provenanceSame
          cases localSame
          rfl

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
      (∀ x y : BareObjectRefusalUp,
          bareObjectRefusalToEventFlow x = bareObjectRefusalToEventFlow y → x = y) ∧
        (BareObjectRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
          BareObjectRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ∧
          (∀ x y : BareObjectRefusalUp,
            bareObjectRefusalFields x = bareObjectRefusalFields y → x = y) := by
  have decodeEncode :
      ∀ h : BHist, bareObjectRefusalDecodeBHist (bareObjectRefusalEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have flowInjective :
      ∀ x y : BareObjectRefusalUp,
        bareObjectRefusalToEventFlow x = bareObjectRefusalToEventFlow y → x = y := by
    intro x y heq
    cases x with
    | mk objectName missingFields refusal witnessAudit ledger transport routes provenance
        localName =>
        cases y with
        | mk objectName' missingFields' refusal' witnessAudit' ledger' transport' routes'
            provenance' localName' =>
            change
              [bareObjectRefusalEncodeBHist objectName,
                bareObjectRefusalEncodeBHist missingFields,
                bareObjectRefusalEncodeBHist refusal,
                bareObjectRefusalEncodeBHist witnessAudit,
                bareObjectRefusalEncodeBHist ledger,
                bareObjectRefusalEncodeBHist transport,
                bareObjectRefusalEncodeBHist routes,
                bareObjectRefusalEncodeBHist provenance,
                bareObjectRefusalEncodeBHist localName] =
              [bareObjectRefusalEncodeBHist objectName',
                bareObjectRefusalEncodeBHist missingFields',
                bareObjectRefusalEncodeBHist refusal',
                bareObjectRefusalEncodeBHist witnessAudit',
                bareObjectRefusalEncodeBHist ledger',
                bareObjectRefusalEncodeBHist transport',
                bareObjectRefusalEncodeBHist routes',
                bareObjectRefusalEncodeBHist provenance',
                bareObjectRefusalEncodeBHist localName'] at heq
            injection heq with hObject t1
            injection t1 with hMissing t2
            injection t2 with hRefusal t3
            injection t3 with hWitness t4
            injection t4 with hLedger t5
            injection t5 with hTransport t6
            injection t6 with hRoutes t7
            injection t7 with hProvenance t8
            injection t8 with hLocal _
            have objectSame : objectName = objectName' := by
              exact Eq.trans (decodeEncode objectName).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hObject)
                  (decodeEncode objectName'))
            have missingSame : missingFields = missingFields' := by
              exact Eq.trans (decodeEncode missingFields).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hMissing)
                  (decodeEncode missingFields'))
            have refusalSame : refusal = refusal' := by
              exact Eq.trans (decodeEncode refusal).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hRefusal)
                  (decodeEncode refusal'))
            have witnessSame : witnessAudit = witnessAudit' := by
              exact Eq.trans (decodeEncode witnessAudit).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hWitness)
                  (decodeEncode witnessAudit'))
            have ledgerSame : ledger = ledger' := by
              exact Eq.trans (decodeEncode ledger).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hLedger)
                  (decodeEncode ledger'))
            have transportSame : transport = transport' := by
              exact Eq.trans (decodeEncode transport).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hTransport)
                  (decodeEncode transport'))
            have routesSame : routes = routes' := by
              exact Eq.trans (decodeEncode routes).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hRoutes)
                  (decodeEncode routes'))
            have provenanceSame : provenance = provenance' := by
              exact Eq.trans (decodeEncode provenance).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hProvenance)
                  (decodeEncode provenance'))
            have localSame : localName = localName' := by
              exact Eq.trans (decodeEncode localName).symm
                (Eq.trans (congrArg bareObjectRefusalDecodeBHist hLocal)
                  (decodeEncode localName'))
            cases objectSame
            cases missingSame
            cases refusalSame
            cases witnessSame
            cases ledgerSame
            cases transportSame
            cases routesSame
            cases provenanceSame
            cases localSame
            rfl
  have distinctWitness :
      BareObjectRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
        BareObjectRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty := by
    intro h
    cases h
  have fieldFaithful :
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
  exact ⟨decodeEncode, flowInjective, distinctWitness, fieldFaithful⟩

end BEDC.Derived.BareObjectRefusalUp
