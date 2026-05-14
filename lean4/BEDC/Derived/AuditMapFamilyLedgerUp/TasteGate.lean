import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapFamilyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapFamilyLedgerUp : Type where
  | mk :
      (familyTag localAudit neighbourLinks positive conditional obstruction frontier transport
        continuation ledger provenance localName : BHist) →
      AuditMapFamilyLedgerUp
  deriving DecidableEq

def auditMapFamilyLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapFamilyLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapFamilyLedgerEncodeBHist h

def auditMapFamilyLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapFamilyLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapFamilyLedgerDecodeBHist tail)

private theorem auditMapFamilyLedgerDecode_encode_bhist :
    ∀ h : BHist, auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapFamilyLedgerFields : AuditMapFamilyLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFamilyLedgerUp.mk familyTag localAudit neighbourLinks positive conditional
      obstruction frontier transport continuation ledger provenance localName =>
      [familyTag, localAudit, neighbourLinks, positive, conditional, obstruction, frontier,
        transport, continuation, ledger, provenance, localName]

def auditMapFamilyLedgerToEventFlow : AuditMapFamilyLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFamilyLedgerUp.mk familyTag localAudit neighbourLinks positive conditional
      obstruction frontier transport continuation ledger provenance localName =>
      [[BMark.b0],
        auditMapFamilyLedgerEncodeBHist familyTag,
        [BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist localAudit,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist neighbourLinks,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist conditional,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapFamilyLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyLedgerEncodeBHist localName]

def auditMapFamilyLedgerFromEventFlow : EventFlow → Option AuditMapFamilyLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | familyTag :: rest1 =>
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
                      | neighbourLinks :: rest5 =>
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
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | ledger ::
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
                                                                                                        (AuditMapFamilyLedgerUp.mk
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            familyTag)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            localAudit)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            neighbourLinks)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            positive)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            conditional)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            obstruction)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            frontier)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            transport)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            continuation)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            ledger)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            provenance)
                                                                                                          (auditMapFamilyLedgerDecodeBHist
                                                                                                            localName))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem auditMapFamilyLedger_round_trip :
    ∀ x : AuditMapFamilyLedgerUp,
      auditMapFamilyLedgerFromEventFlow (auditMapFamilyLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk familyTag localAudit neighbourLinks positive conditional obstruction frontier transport
      continuation ledger provenance localName =>
      change
        some
          (AuditMapFamilyLedgerUp.mk
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist familyTag))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist localAudit))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist neighbourLinks))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist positive))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist conditional))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist obstruction))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist frontier))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist transport))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist continuation))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist ledger))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist provenance))
            (auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist localName))) =
          some
            (AuditMapFamilyLedgerUp.mk familyTag localAudit neighbourLinks positive
              conditional obstruction frontier transport continuation ledger provenance
              localName)
      rw [auditMapFamilyLedgerDecode_encode_bhist familyTag,
        auditMapFamilyLedgerDecode_encode_bhist localAudit,
        auditMapFamilyLedgerDecode_encode_bhist neighbourLinks,
        auditMapFamilyLedgerDecode_encode_bhist positive,
        auditMapFamilyLedgerDecode_encode_bhist conditional,
        auditMapFamilyLedgerDecode_encode_bhist obstruction,
        auditMapFamilyLedgerDecode_encode_bhist frontier,
        auditMapFamilyLedgerDecode_encode_bhist transport,
        auditMapFamilyLedgerDecode_encode_bhist continuation,
        auditMapFamilyLedgerDecode_encode_bhist ledger,
        auditMapFamilyLedgerDecode_encode_bhist provenance,
        auditMapFamilyLedgerDecode_encode_bhist localName]

private theorem auditMapFamilyLedgerToEventFlow_injective {x y : AuditMapFamilyLedgerUp} :
    auditMapFamilyLedgerToEventFlow x = auditMapFamilyLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapFamilyLedgerFromEventFlow (auditMapFamilyLedgerToEventFlow x) =
        auditMapFamilyLedgerFromEventFlow (auditMapFamilyLedgerToEventFlow y) :=
    congrArg auditMapFamilyLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapFamilyLedger_round_trip x).symm
      (Eq.trans hread (auditMapFamilyLedger_round_trip y)))

private theorem AuditMapFamilyLedgerTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : AuditMapFamilyLedgerUp,
      auditMapFamilyLedgerFields x = auditMapFamilyLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk familyTag localAudit neighbourLinks positive conditional obstruction frontier transport
      continuation ledger provenance localName =>
      cases y with
      | mk familyTag' localAudit' neighbourLinks' positive' conditional' obstruction'
          frontier' transport' continuation' ledger' provenance' localName' =>
          injection hfields with hFamilyTag hTail0
          injection hTail0 with hLocalAudit hTail1
          injection hTail1 with hNeighbourLinks hTail2
          injection hTail2 with hPositive hTail3
          injection hTail3 with hConditional hTail4
          injection hTail4 with hObstruction hTail5
          injection hTail5 with hFrontier hTail6
          injection hTail6 with hTransport hTail7
          injection hTail7 with hContinuation hTail8
          injection hTail8 with hLedger hTail9
          injection hTail9 with hProvenance hTail10
          injection hTail10 with hLocalName _hNil
          cases hFamilyTag
          cases hLocalAudit
          cases hNeighbourLinks
          cases hPositive
          cases hConditional
          cases hObstruction
          cases hFrontier
          cases hTransport
          cases hContinuation
          cases hLedger
          cases hProvenance
          cases hLocalName
          rfl

instance auditMapFamilyLedgerBHistCarrier : BHistCarrier AuditMapFamilyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapFamilyLedgerToEventFlow
  fromEventFlow := auditMapFamilyLedgerFromEventFlow

instance auditMapFamilyLedgerChapterTasteGate : ChapterTasteGate AuditMapFamilyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapFamilyLedgerFromEventFlow (auditMapFamilyLedgerToEventFlow x) = some x
    exact auditMapFamilyLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapFamilyLedgerToEventFlow_injective heq)

instance auditMapFamilyLedgerFieldFaithful : FieldFaithful AuditMapFamilyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapFamilyLedgerFields
  field_faithful := AuditMapFamilyLedgerTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate AuditMapFamilyLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapFamilyLedgerChapterTasteGate

theorem AuditMapFamilyLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditMapFamilyLedgerDecodeBHist (auditMapFamilyLedgerEncodeBHist h) = h) ∧
      (∀ x : AuditMapFamilyLedgerUp,
        auditMapFamilyLedgerFromEventFlow (auditMapFamilyLedgerToEventFlow x) = some x) ∧
        (∀ x y : AuditMapFamilyLedgerUp,
          auditMapFamilyLedgerToEventFlow x = auditMapFamilyLedgerToEventFlow y -> x = y) ∧
          auditMapFamilyLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : AuditMapFamilyLedgerUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapFamilyLedgerDecode_encode_bhist
  · constructor
    · exact auditMapFamilyLedger_round_trip
    · constructor
      · intro x y heq
        exact auditMapFamilyLedgerToEventFlow_injective heq
      · constructor
        · rfl
        · exact
            ⟨AuditMapFamilyLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty,
              AuditMapFamilyLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩

end BEDC.Derived.AuditMapFamilyLedgerUp
