import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapFrontierIndexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapFrontierIndexUp : Type where
  | mk :
      (mapTag localAudit neighbouringMap positive conditional obstruction frontier
        synthesisConsumer transport route provenance localName : BHist) →
      AuditMapFrontierIndexUp
  deriving DecidableEq

def auditMapFrontierIndexEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapFrontierIndexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapFrontierIndexEncodeBHist h

def auditMapFrontierIndexDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapFrontierIndexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapFrontierIndexDecodeBHist tail)

private theorem auditMapFrontierIndex_decode_encode_bhist :
    ∀ h : BHist,
      auditMapFrontierIndexDecodeBHist (auditMapFrontierIndexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapFrontierIndexFields : AuditMapFrontierIndexUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFrontierIndexUp.mk mapTag localAudit neighbouringMap positive conditional
      obstruction frontier synthesisConsumer transport route provenance localName =>
      [mapTag, localAudit, neighbouringMap, positive, conditional, obstruction, frontier,
        synthesisConsumer, transport, route, provenance, localName]

def auditMapFrontierIndexToEventFlow : AuditMapFrontierIndexUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFrontierIndexUp.mk mapTag localAudit neighbouringMap positive conditional
      obstruction frontier synthesisConsumer transport route provenance localName =>
      [[BMark.b0],
        auditMapFrontierIndexEncodeBHist mapTag,
        [BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist localAudit,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist neighbouringMap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist conditional,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapFrontierIndexEncodeBHist synthesisConsumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFrontierIndexEncodeBHist localName]

def auditMapFrontierIndexFromEventFlow : EventFlow → Option AuditMapFrontierIndexUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | mapTag :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | localAudit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | neighbouringMap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | positive :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | conditional :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | obstruction :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | frontier :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | synthesisConsumer ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | transport ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | route ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20
                                                                                        with
                                                                                      | [] =>
                                                                                          none
                                                                                      | provenance ::
                                                                                          rest21 =>
                                                                                          match rest21
                                                                                            with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match rest22
                                                                                                with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | localName ::
                                                                                                  rest23 =>
                                                                                                  match rest23
                                                                                                    with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (AuditMapFrontierIndexUp.mk
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            mapTag)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            localAudit)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            neighbouringMap)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            positive)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            conditional)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            obstruction)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            frontier)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            synthesisConsumer)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            transport)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            route)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            provenance)
                                                                                                          (auditMapFrontierIndexDecodeBHist
                                                                                                            localName))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem auditMapFrontierIndex_round_trip :
    ∀ x : AuditMapFrontierIndexUp,
      auditMapFrontierIndexFromEventFlow (auditMapFrontierIndexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk mapTag localAudit neighbouringMap positive conditional obstruction frontier
      synthesisConsumer transport route provenance localName =>
      change
        some
          (AuditMapFrontierIndexUp.mk
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist mapTag))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist localAudit))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist neighbouringMap))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist positive))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist conditional))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist obstruction))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist frontier))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist synthesisConsumer))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist transport))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist route))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist provenance))
            (auditMapFrontierIndexDecodeBHist
              (auditMapFrontierIndexEncodeBHist localName))) =
          some
            (AuditMapFrontierIndexUp.mk mapTag localAudit neighbouringMap positive
              conditional obstruction frontier synthesisConsumer transport route provenance
              localName)
      rw [auditMapFrontierIndex_decode_encode_bhist mapTag,
        auditMapFrontierIndex_decode_encode_bhist localAudit,
        auditMapFrontierIndex_decode_encode_bhist neighbouringMap,
        auditMapFrontierIndex_decode_encode_bhist positive,
        auditMapFrontierIndex_decode_encode_bhist conditional,
        auditMapFrontierIndex_decode_encode_bhist obstruction,
        auditMapFrontierIndex_decode_encode_bhist frontier,
        auditMapFrontierIndex_decode_encode_bhist synthesisConsumer,
        auditMapFrontierIndex_decode_encode_bhist transport,
        auditMapFrontierIndex_decode_encode_bhist route,
        auditMapFrontierIndex_decode_encode_bhist provenance,
        auditMapFrontierIndex_decode_encode_bhist localName]

private theorem auditMapFrontierIndexToEventFlow_injective
    {x y : AuditMapFrontierIndexUp} :
    auditMapFrontierIndexToEventFlow x = auditMapFrontierIndexToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapFrontierIndexFromEventFlow (auditMapFrontierIndexToEventFlow x) =
        auditMapFrontierIndexFromEventFlow (auditMapFrontierIndexToEventFlow y) :=
    congrArg auditMapFrontierIndexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapFrontierIndex_round_trip x).symm
      (Eq.trans hread (auditMapFrontierIndex_round_trip y)))

instance auditMapFrontierIndexBHistCarrier : BHistCarrier AuditMapFrontierIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapFrontierIndexToEventFlow
  fromEventFlow := auditMapFrontierIndexFromEventFlow

instance auditMapFrontierIndexChapterTasteGate :
    ChapterTasteGate AuditMapFrontierIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapFrontierIndexFromEventFlow (auditMapFrontierIndexToEventFlow x) = some x
    exact auditMapFrontierIndex_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapFrontierIndexToEventFlow_injective heq)

instance auditMapFrontierIndexFieldFaithful : FieldFaithful AuditMapFrontierIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapFrontierIndexFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk mapTag localAudit neighbouringMap positive conditional obstruction frontier
        synthesisConsumer transport route provenance localName =>
        cases y with
        | mk mapTag' localAudit' neighbouringMap' positive' conditional' obstruction'
            frontier' synthesisConsumer' transport' route' provenance' localName' =>
            change
              [mapTag, localAudit, neighbouringMap, positive, conditional, obstruction,
                  frontier, synthesisConsumer, transport, route, provenance, localName] =
                [mapTag', localAudit', neighbouringMap', positive', conditional',
                  obstruction', frontier', synthesisConsumer', transport', route',
                  provenance', localName'] at hfields
            injection hfields with hMapTag hTail0
            injection hTail0 with hLocalAudit hTail1
            injection hTail1 with hNeighbouringMap hTail2
            injection hTail2 with hPositive hTail3
            injection hTail3 with hConditional hTail4
            injection hTail4 with hObstruction hTail5
            injection hTail5 with hFrontier hTail6
            injection hTail6 with hSynthesisConsumer hTail7
            injection hTail7 with hTransport hTail8
            injection hTail8 with hRoute hTail9
            injection hTail9 with hProvenance hTail10
            injection hTail10 with hLocalName _hNil
            cases hMapTag
            cases hLocalAudit
            cases hNeighbouringMap
            cases hPositive
            cases hConditional
            cases hObstruction
            cases hFrontier
            cases hSynthesisConsumer
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hLocalName
            rfl

instance auditMapFrontierIndexNontrivial : Nontrivial AuditMapFrontierIndexUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapFrontierIndexUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AuditMapFrontierIndexUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AuditMapFrontierIndexTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditMapFrontierIndexDecodeBHist (auditMapFrontierIndexEncodeBHist h) = h) ∧
      (∀ x : AuditMapFrontierIndexUp,
        auditMapFrontierIndexFromEventFlow (auditMapFrontierIndexToEventFlow x) = some x) ∧
      (∀ x y : AuditMapFrontierIndexUp,
        auditMapFrontierIndexToEventFlow x = auditMapFrontierIndexToEventFlow y → x = y) ∧
        auditMapFrontierIndexEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : AuditMapFrontierIndexUp, auditMapFrontierIndexFields x =
          auditMapFrontierIndexFields y → x = y) ∧
          (∃ x y : AuditMapFrontierIndexUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapFrontierIndex_decode_encode_bhist
  · constructor
    · exact auditMapFrontierIndex_round_trip
    · constructor
      · intro x y heq
        exact auditMapFrontierIndexToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · intro x y hfields
            cases x with
            | mk mapTag localAudit neighbouringMap positive conditional obstruction frontier
                synthesisConsumer transport route provenance localName =>
                cases y with
                | mk mapTag' localAudit' neighbouringMap' positive' conditional' obstruction'
                    frontier' synthesisConsumer' transport' route' provenance' localName' =>
                    change
                      [mapTag, localAudit, neighbouringMap, positive, conditional, obstruction,
                          frontier, synthesisConsumer, transport, route, provenance, localName] =
                        [mapTag', localAudit', neighbouringMap', positive', conditional',
                          obstruction', frontier', synthesisConsumer', transport', route',
                          provenance', localName'] at hfields
                    injection hfields with hMapTag hTail0
                    injection hTail0 with hLocalAudit hTail1
                    injection hTail1 with hNeighbouringMap hTail2
                    injection hTail2 with hPositive hTail3
                    injection hTail3 with hConditional hTail4
                    injection hTail4 with hObstruction hTail5
                    injection hTail5 with hFrontier hTail6
                    injection hTail6 with hSynthesisConsumer hTail7
                    injection hTail7 with hTransport hTail8
                    injection hTail8 with hRoute hTail9
                    injection hTail9 with hProvenance hTail10
                    injection hTail10 with hLocalName _hNil
                    cases hMapTag
                    cases hLocalAudit
                    cases hNeighbouringMap
                    cases hPositive
                    cases hConditional
                    cases hObstruction
                    cases hFrontier
                    cases hSynthesisConsumer
                    cases hTransport
                    cases hRoute
                    cases hProvenance
                    cases hLocalName
                    rfl
          · exact
              ⟨AuditMapFrontierIndexUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                AuditMapFrontierIndexUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.AuditMapFrontierIndexUp
