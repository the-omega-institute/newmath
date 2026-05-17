import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapRouteBudgetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapRouteBudgetUp : Type where
  | mk (eventFlow sourceChannel recognizer certificateGate reportBoundary cannotClaim
      transport continuation provenance localName : BHist) : AuditMapRouteBudgetUp
  deriving DecidableEq

def auditMapRouteBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapRouteBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapRouteBudgetEncodeBHist h

def auditMapRouteBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapRouteBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapRouteBudgetDecodeBHist tail)

private theorem auditMapRouteBudgetDecode_encode_bhist :
    ∀ h : BHist,
      auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem auditMapRouteBudget_mk_congr
    {eventFlow eventFlow' sourceChannel sourceChannel' recognizer recognizer'
      certificateGate certificateGate' reportBoundary reportBoundary' cannotClaim cannotClaim'
      transport transport' continuation continuation' provenance provenance' localName
      localName' : BHist}
    (hEventFlow : eventFlow' = eventFlow)
    (hSourceChannel : sourceChannel' = sourceChannel)
    (hRecognizer : recognizer' = recognizer)
    (hCertificateGate : certificateGate' = certificateGate)
    (hReportBoundary : reportBoundary' = reportBoundary)
    (hCannotClaim : cannotClaim' = cannotClaim)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    AuditMapRouteBudgetUp.mk eventFlow' sourceChannel' recognizer' certificateGate'
        reportBoundary' cannotClaim' transport' continuation' provenance' localName' =
      AuditMapRouteBudgetUp.mk eventFlow sourceChannel recognizer certificateGate
        reportBoundary cannotClaim transport continuation provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEventFlow
  cases hSourceChannel
  cases hRecognizer
  cases hCertificateGate
  cases hReportBoundary
  cases hCannotClaim
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

def auditMapRouteBudgetToEventFlow : AuditMapRouteBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapRouteBudgetUp.mk eventFlow sourceChannel recognizer certificateGate
      reportBoundary cannotClaim transport continuation provenance localName =>
      [[BMark.b0],
        auditMapRouteBudgetEncodeBHist eventFlow,
        [BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist sourceChannel,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist recognizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist certificateGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist reportBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapRouteBudgetEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteBudgetEncodeBHist localName]

def auditMapRouteBudgetFromEventFlow : EventFlow → Option AuditMapRouteBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | eventFlow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceChannel :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recognizer :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | certificateGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | reportBoundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | cannotClaim :: rest11 =>
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
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (AuditMapRouteBudgetUp.mk
                                                                                          (auditMapRouteBudgetDecodeBHist eventFlow)
                                                                                          (auditMapRouteBudgetDecodeBHist sourceChannel)
                                                                                          (auditMapRouteBudgetDecodeBHist recognizer)
                                                                                          (auditMapRouteBudgetDecodeBHist certificateGate)
                                                                                          (auditMapRouteBudgetDecodeBHist reportBoundary)
                                                                                          (auditMapRouteBudgetDecodeBHist cannotClaim)
                                                                                          (auditMapRouteBudgetDecodeBHist transport)
                                                                                          (auditMapRouteBudgetDecodeBHist continuation)
                                                                                          (auditMapRouteBudgetDecodeBHist provenance)
                                                                                          (auditMapRouteBudgetDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem auditMapRouteBudget_round_trip :
    ∀ x : AuditMapRouteBudgetUp,
      auditMapRouteBudgetFromEventFlow
        (auditMapRouteBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eventFlow sourceChannel recognizer certificateGate reportBoundary cannotClaim
      transport continuation provenance localName =>
      change
        some
          (AuditMapRouteBudgetUp.mk
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist eventFlow))
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist sourceChannel))
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist recognizer))
            (auditMapRouteBudgetDecodeBHist
              (auditMapRouteBudgetEncodeBHist certificateGate))
            (auditMapRouteBudgetDecodeBHist
              (auditMapRouteBudgetEncodeBHist reportBoundary))
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist cannotClaim))
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist transport))
            (auditMapRouteBudgetDecodeBHist
              (auditMapRouteBudgetEncodeBHist continuation))
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist provenance))
            (auditMapRouteBudgetDecodeBHist (auditMapRouteBudgetEncodeBHist localName))) =
          some
            (AuditMapRouteBudgetUp.mk eventFlow sourceChannel recognizer certificateGate
              reportBoundary cannotClaim transport continuation provenance localName)
      exact
        congrArg some
          (auditMapRouteBudget_mk_congr
            (auditMapRouteBudgetDecode_encode_bhist eventFlow)
            (auditMapRouteBudgetDecode_encode_bhist sourceChannel)
            (auditMapRouteBudgetDecode_encode_bhist recognizer)
            (auditMapRouteBudgetDecode_encode_bhist certificateGate)
            (auditMapRouteBudgetDecode_encode_bhist reportBoundary)
            (auditMapRouteBudgetDecode_encode_bhist cannotClaim)
            (auditMapRouteBudgetDecode_encode_bhist transport)
            (auditMapRouteBudgetDecode_encode_bhist continuation)
            (auditMapRouteBudgetDecode_encode_bhist provenance)
            (auditMapRouteBudgetDecode_encode_bhist localName))

private theorem auditMapRouteBudgetToEventFlow_injective
    {x y : AuditMapRouteBudgetUp} :
    auditMapRouteBudgetToEventFlow x =
      auditMapRouteBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapRouteBudgetFromEventFlow
          (auditMapRouteBudgetToEventFlow x) =
        auditMapRouteBudgetFromEventFlow
          (auditMapRouteBudgetToEventFlow y) :=
    congrArg auditMapRouteBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapRouteBudget_round_trip x).symm
      (Eq.trans hread (auditMapRouteBudget_round_trip y)))

def auditMapRouteBudgetFields : AuditMapRouteBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapRouteBudgetUp.mk eventFlow sourceChannel recognizer certificateGate
      reportBoundary cannotClaim transport continuation provenance localName =>
      [eventFlow, sourceChannel, recognizer, certificateGate, reportBoundary, cannotClaim,
        transport, continuation, provenance, localName]

instance auditMapRouteBudgetBHistCarrier :
    BHistCarrier AuditMapRouteBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapRouteBudgetToEventFlow
  fromEventFlow := auditMapRouteBudgetFromEventFlow

instance auditMapRouteBudgetChapterTasteGate :
    ChapterTasteGate AuditMapRouteBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapRouteBudgetFromEventFlow (auditMapRouteBudgetToEventFlow x) = some x
    exact auditMapRouteBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapRouteBudgetToEventFlow_injective heq)

instance auditMapRouteBudgetFieldFaithful :
    FieldFaithful AuditMapRouteBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapRouteBudgetFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk eventFlow sourceChannel recognizer certificateGate reportBoundary cannotClaim
        transport continuation provenance localName =>
        cases y with
        | mk eventFlow' sourceChannel' recognizer' certificateGate' reportBoundary'
            cannotClaim' transport' continuation' provenance' localName' =>
            cases hfields
            rfl

instance auditMapRouteBudgetNontrivial :
    Nontrivial AuditMapRouteBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapRouteBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditMapRouteBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditMapRouteBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapRouteBudgetChapterTasteGate

theorem AuditMapRouteBudgetUp_single_carrier_alignment :
    (∀ h : BHist, auditMapRouteBudgetDecodeBHist
      (auditMapRouteBudgetEncodeBHist h) = h) ∧
      (∀ x : AuditMapRouteBudgetUp,
        auditMapRouteBudgetFromEventFlow (auditMapRouteBudgetToEventFlow x) = some x) ∧
      (∀ x y : AuditMapRouteBudgetUp,
        auditMapRouteBudgetToEventFlow x = auditMapRouteBudgetToEventFlow y -> x = y) ∧
      auditMapRouteBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact auditMapRouteBudgetDecode_encode_bhist
  · constructor
    · exact auditMapRouteBudget_round_trip
    · constructor
      · intro x y heq
        exact auditMapRouteBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditMapRouteBudgetUp.TasteGate
