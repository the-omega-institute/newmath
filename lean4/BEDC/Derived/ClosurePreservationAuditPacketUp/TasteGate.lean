import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosurePreservationAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosurePreservationAuditPacketUp : Type where
  | mk :
      (anchor ledger shift substitute variableSubstitution fullSubstitution betaStep betaStar
        replay siblingRoutes transport continuation provenance localName : BHist) →
      ClosurePreservationAuditPacketUp
  deriving DecidableEq

def closurePreservationAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closurePreservationAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closurePreservationAuditPacketEncodeBHist h

def closurePreservationAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closurePreservationAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closurePreservationAuditPacketDecodeBHist tail)

private theorem closurePreservationAuditPacket_decode_encode_bhist :
    ∀ h : BHist,
      closurePreservationAuditPacketDecodeBHist
        (closurePreservationAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closurePreservationAuditPacketToEventFlow :
    ClosurePreservationAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosurePreservationAuditPacketUp.mk anchor ledger shift substitute variableSubstitution
      fullSubstitution betaStep betaStar replay siblingRoutes transport continuation provenance
      localName =>
      [[BMark.b0],
        closurePreservationAuditPacketEncodeBHist anchor,
        [BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist shift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist substitute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist variableSubstitution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist fullSubstitution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist betaStep,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closurePreservationAuditPacketEncodeBHist betaStar,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist siblingRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditPacketEncodeBHist localName]

def closurePreservationAuditPacketFromEventFlow :
    EventFlow → Option ClosurePreservationAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | anchor :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | ledger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | shift :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | substitute :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | variableSubstitution :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | fullSubstitution :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | betaStep :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | betaStar ::
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
                                                                      | replay ::
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
                                                                              | siblingRoutes ::
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
                                                                                      | transport ::
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
                                                                                              | continuation ::
                                                                                                  rest23 =>
                                                                                                  match rest23
                                                                                                    with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match rest24
                                                                                                        with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | provenance ::
                                                                                                          rest25 =>
                                                                                                          match rest25
                                                                                                            with
                                                                                                          | [] =>
                                                                                                              none
                                                                                                          | _tag13 ::
                                                                                                              rest26 =>
                                                                                                              match rest26
                                                                                                                with
                                                                                                              | [] =>
                                                                                                                  none
                                                                                                              | localName ::
                                                                                                                  rest27 =>
                                                                                                                  match rest27
                                                                                                                    with
                                                                                                                  | [] =>
                                                                                                                      some
                                                                                                                        (ClosurePreservationAuditPacketUp.mk
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            anchor)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            ledger)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            shift)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            substitute)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            variableSubstitution)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            fullSubstitution)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            betaStep)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            betaStar)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            replay)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            siblingRoutes)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            transport)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            continuation)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            provenance)
                                                                                                                          (closurePreservationAuditPacketDecodeBHist
                                                                                                                            localName))
                                                                                                                  | _ :: _ =>
                                                                                                                      none

private theorem closurePreservationAuditPacket_round_trip :
    ∀ x : ClosurePreservationAuditPacketUp,
      closurePreservationAuditPacketFromEventFlow
        (closurePreservationAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk anchor ledger shift substitute variableSubstitution fullSubstitution betaStep betaStar
      replay siblingRoutes transport continuation provenance localName =>
      change
        some
          (ClosurePreservationAuditPacketUp.mk
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist anchor))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist ledger))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist shift))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist substitute))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist variableSubstitution))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist fullSubstitution))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist betaStep))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist betaStar))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist replay))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist siblingRoutes))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist transport))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist continuation))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist provenance))
            (closurePreservationAuditPacketDecodeBHist
              (closurePreservationAuditPacketEncodeBHist localName))) =
          some
            (ClosurePreservationAuditPacketUp.mk anchor ledger shift substitute
              variableSubstitution fullSubstitution betaStep betaStar replay siblingRoutes
              transport continuation provenance localName)
      rw [closurePreservationAuditPacket_decode_encode_bhist anchor,
        closurePreservationAuditPacket_decode_encode_bhist ledger,
        closurePreservationAuditPacket_decode_encode_bhist shift,
        closurePreservationAuditPacket_decode_encode_bhist substitute,
        closurePreservationAuditPacket_decode_encode_bhist variableSubstitution,
        closurePreservationAuditPacket_decode_encode_bhist fullSubstitution,
        closurePreservationAuditPacket_decode_encode_bhist betaStep,
        closurePreservationAuditPacket_decode_encode_bhist betaStar,
        closurePreservationAuditPacket_decode_encode_bhist replay,
        closurePreservationAuditPacket_decode_encode_bhist siblingRoutes,
        closurePreservationAuditPacket_decode_encode_bhist transport,
        closurePreservationAuditPacket_decode_encode_bhist continuation,
        closurePreservationAuditPacket_decode_encode_bhist provenance,
        closurePreservationAuditPacket_decode_encode_bhist localName]

private theorem closurePreservationAuditPacketToEventFlow_injective
    {x y : ClosurePreservationAuditPacketUp} :
    closurePreservationAuditPacketToEventFlow x =
      closurePreservationAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closurePreservationAuditPacketFromEventFlow
          (closurePreservationAuditPacketToEventFlow x) =
        closurePreservationAuditPacketFromEventFlow
          (closurePreservationAuditPacketToEventFlow y) :=
    congrArg closurePreservationAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closurePreservationAuditPacket_round_trip x).symm
      (Eq.trans hread (closurePreservationAuditPacket_round_trip y)))

instance closurePreservationAuditPacketBHistCarrier :
    BHistCarrier ClosurePreservationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closurePreservationAuditPacketToEventFlow
  fromEventFlow := closurePreservationAuditPacketFromEventFlow

instance closurePreservationAuditPacketChapterTasteGate :
    ChapterTasteGate ClosurePreservationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closurePreservationAuditPacketFromEventFlow
        (closurePreservationAuditPacketToEventFlow x) = some x
    exact closurePreservationAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closurePreservationAuditPacketToEventFlow_injective heq)

instance closurePreservationAuditPacketFieldFaithful :
    FieldFaithful ClosurePreservationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | ClosurePreservationAuditPacketUp.mk anchor ledger shift substitute variableSubstitution
        fullSubstitution betaStep betaStar replay siblingRoutes transport continuation provenance
        localName =>
        [anchor, ledger, shift, substitute, variableSubstitution, fullSubstitution, betaStep,
          betaStar, replay, siblingRoutes, transport, continuation, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk anchor ledger shift substitute variableSubstitution fullSubstitution betaStep betaStar
        replay siblingRoutes transport continuation provenance localName =>
        cases y with
        | mk anchor' ledger' shift' substitute' variableSubstitution' fullSubstitution'
            betaStep' betaStar' replay' siblingRoutes' transport' continuation' provenance'
            localName' =>
            injection hfields with hAnchor hTail0
            injection hTail0 with hLedger hTail1
            injection hTail1 with hShift hTail2
            injection hTail2 with hSubstitute hTail3
            injection hTail3 with hVariableSubstitution hTail4
            injection hTail4 with hFullSubstitution hTail5
            injection hTail5 with hBetaStep hTail6
            injection hTail6 with hBetaStar hTail7
            injection hTail7 with hReplay hTail8
            injection hTail8 with hSiblingRoutes hTail9
            injection hTail9 with hTransport hTail10
            injection hTail10 with hContinuation hTail11
            injection hTail11 with hProvenance hTail12
            injection hTail12 with hLocalName _hNil
            cases hAnchor
            cases hLedger
            cases hShift
            cases hSubstitute
            cases hVariableSubstitution
            cases hFullSubstitution
            cases hBetaStep
            cases hBetaStar
            cases hReplay
            cases hSiblingRoutes
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hLocalName
            rfl

theorem ClosurePreservationAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closurePreservationAuditPacketDecodeBHist
        (closurePreservationAuditPacketEncodeBHist h) = h) ∧
      (∀ x : ClosurePreservationAuditPacketUp,
        closurePreservationAuditPacketFromEventFlow
          (closurePreservationAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : ClosurePreservationAuditPacketUp,
          closurePreservationAuditPacketToEventFlow x =
            closurePreservationAuditPacketToEventFlow y → x = y) ∧
          closurePreservationAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closurePreservationAuditPacket_decode_encode_bhist
  · constructor
    · exact closurePreservationAuditPacket_round_trip
    · constructor
      · intro x y heq
        exact closurePreservationAuditPacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosurePreservationAuditPacketUp
