import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapFamilyObligationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapFamilyObligationLedgerUp : Type where
  | mk :
      (familyTag positive conditional obstruction frontier crossModuleUse transport replay
        provenance localName : BHist) →
      AuditMapFamilyObligationLedgerUp
  deriving DecidableEq

def auditMapFamilyObligationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapFamilyObligationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapFamilyObligationLedgerEncodeBHist h

def auditMapFamilyObligationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapFamilyObligationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapFamilyObligationLedgerDecodeBHist tail)

private theorem auditMapFamilyObligationLedger_decode_encode_bhist :
    ∀ h : BHist,
      auditMapFamilyObligationLedgerDecodeBHist
        (auditMapFamilyObligationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapFamilyObligationLedgerToEventFlow :
    AuditMapFamilyObligationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFamilyObligationLedgerUp.mk familyTag positive conditional obstruction frontier
      crossModuleUse transport replay provenance localName =>
      [[BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist familyTag,
        [BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist conditional,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist crossModuleUse,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyObligationLedgerEncodeBHist localName]

def auditMapFamilyObligationLedgerFromEventFlow :
    EventFlow → Option AuditMapFamilyObligationLedgerUp
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
              | positive :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | conditional :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | obstruction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | frontier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | crossModuleUse :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay ::
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
                                                                      | provenance ::
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
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (AuditMapFamilyObligationLedgerUp.mk
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            familyTag)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            positive)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            conditional)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            obstruction)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            frontier)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            crossModuleUse)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            transport)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            replay)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            provenance)
                                                                                          (auditMapFamilyObligationLedgerDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem auditMapFamilyObligationLedger_round_trip :
    ∀ x : AuditMapFamilyObligationLedgerUp,
      auditMapFamilyObligationLedgerFromEventFlow
        (auditMapFamilyObligationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk familyTag positive conditional obstruction frontier crossModuleUse transport replay
      provenance localName =>
      change
        some
          (AuditMapFamilyObligationLedgerUp.mk
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist familyTag))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist positive))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist conditional))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist obstruction))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist frontier))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist crossModuleUse))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist transport))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist replay))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist provenance))
            (auditMapFamilyObligationLedgerDecodeBHist
              (auditMapFamilyObligationLedgerEncodeBHist localName))) =
          some
            (AuditMapFamilyObligationLedgerUp.mk familyTag positive conditional obstruction
              frontier crossModuleUse transport replay provenance localName)
      rw [auditMapFamilyObligationLedger_decode_encode_bhist familyTag,
        auditMapFamilyObligationLedger_decode_encode_bhist positive,
        auditMapFamilyObligationLedger_decode_encode_bhist conditional,
        auditMapFamilyObligationLedger_decode_encode_bhist obstruction,
        auditMapFamilyObligationLedger_decode_encode_bhist frontier,
        auditMapFamilyObligationLedger_decode_encode_bhist crossModuleUse,
        auditMapFamilyObligationLedger_decode_encode_bhist transport,
        auditMapFamilyObligationLedger_decode_encode_bhist replay,
        auditMapFamilyObligationLedger_decode_encode_bhist provenance,
        auditMapFamilyObligationLedger_decode_encode_bhist localName]

private theorem auditMapFamilyObligationLedgerToEventFlow_injective
    {x y : AuditMapFamilyObligationLedgerUp} :
    auditMapFamilyObligationLedgerToEventFlow x =
      auditMapFamilyObligationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapFamilyObligationLedgerFromEventFlow
          (auditMapFamilyObligationLedgerToEventFlow x) =
        auditMapFamilyObligationLedgerFromEventFlow
          (auditMapFamilyObligationLedgerToEventFlow y) :=
    congrArg auditMapFamilyObligationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapFamilyObligationLedger_round_trip x).symm
      (Eq.trans hread (auditMapFamilyObligationLedger_round_trip y)))

instance auditMapFamilyObligationLedgerBHistCarrier :
    BHistCarrier AuditMapFamilyObligationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapFamilyObligationLedgerToEventFlow
  fromEventFlow := auditMapFamilyObligationLedgerFromEventFlow

instance auditMapFamilyObligationLedgerChapterTasteGate :
    ChapterTasteGate AuditMapFamilyObligationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditMapFamilyObligationLedgerFromEventFlow
        (auditMapFamilyObligationLedgerToEventFlow x) = some x
    exact auditMapFamilyObligationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapFamilyObligationLedgerToEventFlow_injective heq)

instance auditMapFamilyObligationLedgerFieldFaithful :
    FieldFaithful AuditMapFamilyObligationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | AuditMapFamilyObligationLedgerUp.mk familyTag positive conditional obstruction frontier
        crossModuleUse transport replay provenance localName =>
        [familyTag, positive, conditional, obstruction, frontier, crossModuleUse, transport,
          replay, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk familyTag positive conditional obstruction frontier crossModuleUse transport replay
        provenance localName =>
        cases y with
        | mk familyTag' positive' conditional' obstruction' frontier' crossModuleUse'
            transport' replay' provenance' localName' =>
            injection hfields with hFamilyTag hTail0
            injection hTail0 with hPositive hTail1
            injection hTail1 with hConditional hTail2
            injection hTail2 with hObstruction hTail3
            injection hTail3 with hFrontier hTail4
            injection hTail4 with hCrossModuleUse hTail5
            injection hTail5 with hTransport hTail6
            injection hTail6 with hReplay hTail7
            injection hTail7 with hProvenance hTail8
            injection hTail8 with hLocalName _hNil
            cases hFamilyTag
            cases hPositive
            cases hConditional
            cases hObstruction
            cases hFrontier
            cases hCrossModuleUse
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

theorem AuditMapFamilyObligationLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapFamilyObligationLedgerDecodeBHist
        (auditMapFamilyObligationLedgerEncodeBHist h) = h) ∧
      (∀ x : AuditMapFamilyObligationLedgerUp,
        auditMapFamilyObligationLedgerFromEventFlow
          (auditMapFamilyObligationLedgerToEventFlow x) = some x) ∧
        (∀ x y : AuditMapFamilyObligationLedgerUp,
          auditMapFamilyObligationLedgerToEventFlow x =
            auditMapFamilyObligationLedgerToEventFlow y → x = y) ∧
          auditMapFamilyObligationLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapFamilyObligationLedger_decode_encode_bhist
  · constructor
    · exact auditMapFamilyObligationLedger_round_trip
    · constructor
      · intro x y heq
        exact auditMapFamilyObligationLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditMapFamilyObligationLedgerUp
