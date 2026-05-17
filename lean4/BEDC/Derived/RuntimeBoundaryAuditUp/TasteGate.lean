import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuntimeBoundaryAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuntimeBoundaryAuditUp : Type where
  | mk :
      (selfDescription candidateBoundary runtimeRefusal metaObstruction reflectionLimit auditLedger
        transport routes provenance nameCert : BHist) →
      RuntimeBoundaryAuditUp

def runtimeBoundaryAuditEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: runtimeBoundaryAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: runtimeBoundaryAuditEncodeBHist h

def runtimeBoundaryAuditDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (runtimeBoundaryAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (runtimeBoundaryAuditDecodeBHist tail)

private theorem runtimeBoundaryAudit_decode_encode_bhist :
    ∀ h : BHist,
      runtimeBoundaryAuditDecodeBHist (runtimeBoundaryAuditEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def runtimeBoundaryAuditToEventFlow : RuntimeBoundaryAuditUp → EventFlow
  | RuntimeBoundaryAuditUp.mk selfDescription candidateBoundary runtimeRefusal metaObstruction
      reflectionLimit auditLedger transport routes provenance nameCert =>
      [[BMark.b0],
        runtimeBoundaryAuditEncodeBHist selfDescription,
        [BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist candidateBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist runtimeRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist metaObstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist reflectionLimit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist auditLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        runtimeBoundaryAuditEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        runtimeBoundaryAuditEncodeBHist nameCert]

private def runtimeBoundaryAuditDecodePacket
    (selfDescription candidateBoundary runtimeRefusal metaObstruction reflectionLimit auditLedger
      transport routes provenance nameCert : RawEvent) : RuntimeBoundaryAuditUp :=
  RuntimeBoundaryAuditUp.mk
    (runtimeBoundaryAuditDecodeBHist selfDescription)
    (runtimeBoundaryAuditDecodeBHist candidateBoundary)
    (runtimeBoundaryAuditDecodeBHist runtimeRefusal)
    (runtimeBoundaryAuditDecodeBHist metaObstruction)
    (runtimeBoundaryAuditDecodeBHist reflectionLimit)
    (runtimeBoundaryAuditDecodeBHist auditLedger)
    (runtimeBoundaryAuditDecodeBHist transport)
    (runtimeBoundaryAuditDecodeBHist routes)
    (runtimeBoundaryAuditDecodeBHist provenance)
    (runtimeBoundaryAuditDecodeBHist nameCert)

def runtimeBoundaryAuditFromEventFlow :
    EventFlow → Option RuntimeBoundaryAuditUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selfDescription :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | candidateBoundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | runtimeRefusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | metaObstruction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | reflectionLimit :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | auditLedger :: rest11 =>
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
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18 with
                                                                              | [] => none
                                                                              | nameCert ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (runtimeBoundaryAuditDecodePacket
                                                                                          selfDescription
                                                                                          candidateBoundary
                                                                                          runtimeRefusal
                                                                                          metaObstruction
                                                                                          reflectionLimit
                                                                                          auditLedger
                                                                                          transport
                                                                                          routes
                                                                                          provenance
                                                                                          nameCert)
                                                                                  | _ :: _ =>
                                                                                      none

private theorem runtimeBoundaryAuditMkCongr
    {selfDescription selfDescription' candidateBoundary candidateBoundary' runtimeRefusal
      runtimeRefusal' metaObstruction metaObstruction' reflectionLimit reflectionLimit'
      auditLedger auditLedger' transport transport' routes routes' provenance provenance'
      nameCert nameCert' : BHist}
    (hSelfDescription : selfDescription' = selfDescription)
    (hCandidateBoundary : candidateBoundary' = candidateBoundary)
    (hRuntimeRefusal : runtimeRefusal' = runtimeRefusal)
    (hMetaObstruction : metaObstruction' = metaObstruction)
    (hReflectionLimit : reflectionLimit' = reflectionLimit)
    (hAuditLedger : auditLedger' = auditLedger)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    RuntimeBoundaryAuditUp.mk selfDescription' candidateBoundary' runtimeRefusal'
        metaObstruction' reflectionLimit' auditLedger' transport' routes' provenance'
        nameCert' =
      RuntimeBoundaryAuditUp.mk selfDescription candidateBoundary runtimeRefusal
        metaObstruction reflectionLimit auditLedger transport routes provenance nameCert := by
  cases hSelfDescription
  cases hCandidateBoundary
  cases hRuntimeRefusal
  cases hMetaObstruction
  cases hReflectionLimit
  cases hAuditLedger
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private theorem runtimeBoundaryAudit_round_trip :
    ∀ x : RuntimeBoundaryAuditUp,
      runtimeBoundaryAuditFromEventFlow (runtimeBoundaryAuditToEventFlow x) = some x := by
  intro x
  cases x with
  | mk selfDescription candidateBoundary runtimeRefusal metaObstruction reflectionLimit auditLedger
      transport routes provenance nameCert =>
      change
        some
          (runtimeBoundaryAuditDecodePacket
            (runtimeBoundaryAuditEncodeBHist selfDescription)
            (runtimeBoundaryAuditEncodeBHist candidateBoundary)
            (runtimeBoundaryAuditEncodeBHist runtimeRefusal)
            (runtimeBoundaryAuditEncodeBHist metaObstruction)
            (runtimeBoundaryAuditEncodeBHist reflectionLimit)
            (runtimeBoundaryAuditEncodeBHist auditLedger)
            (runtimeBoundaryAuditEncodeBHist transport)
            (runtimeBoundaryAuditEncodeBHist routes)
            (runtimeBoundaryAuditEncodeBHist provenance)
            (runtimeBoundaryAuditEncodeBHist nameCert)) =
          some
            (RuntimeBoundaryAuditUp.mk selfDescription candidateBoundary runtimeRefusal
              metaObstruction reflectionLimit auditLedger transport routes provenance nameCert)
      unfold runtimeBoundaryAuditDecodePacket
      exact
        congrArg some
          (runtimeBoundaryAuditMkCongr
            (runtimeBoundaryAudit_decode_encode_bhist selfDescription)
            (runtimeBoundaryAudit_decode_encode_bhist candidateBoundary)
            (runtimeBoundaryAudit_decode_encode_bhist runtimeRefusal)
            (runtimeBoundaryAudit_decode_encode_bhist metaObstruction)
            (runtimeBoundaryAudit_decode_encode_bhist reflectionLimit)
            (runtimeBoundaryAudit_decode_encode_bhist auditLedger)
            (runtimeBoundaryAudit_decode_encode_bhist transport)
            (runtimeBoundaryAudit_decode_encode_bhist routes)
            (runtimeBoundaryAudit_decode_encode_bhist provenance)
            (runtimeBoundaryAudit_decode_encode_bhist nameCert))

private theorem runtimeBoundaryAuditToEventFlow_injective
    {x y : RuntimeBoundaryAuditUp} :
    runtimeBoundaryAuditToEventFlow x = runtimeBoundaryAuditToEventFlow y → x = y := by
  intro heq
  have hread :
      runtimeBoundaryAuditFromEventFlow (runtimeBoundaryAuditToEventFlow x) =
        runtimeBoundaryAuditFromEventFlow (runtimeBoundaryAuditToEventFlow y) :=
    congrArg runtimeBoundaryAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (runtimeBoundaryAudit_round_trip x).symm
      (Eq.trans hread (runtimeBoundaryAudit_round_trip y)))

private def runtimeBoundaryAuditFields :
    RuntimeBoundaryAuditUp → List BHist
  | RuntimeBoundaryAuditUp.mk selfDescription candidateBoundary runtimeRefusal metaObstruction
      reflectionLimit auditLedger transport routes provenance nameCert =>
      [selfDescription, candidateBoundary, runtimeRefusal, metaObstruction, reflectionLimit,
        auditLedger, transport, routes, provenance, nameCert]

private theorem runtimeBoundaryAudit_field_faithful :
    ∀ x y : RuntimeBoundaryAuditUp,
      runtimeBoundaryAuditFields x = runtimeBoundaryAuditFields y → x = y := by
  intro x y hfields
  cases x with
  | mk selfDescription candidateBoundary runtimeRefusal metaObstruction reflectionLimit auditLedger
      transport routes provenance nameCert =>
      cases y with
      | mk selfDescription' candidateBoundary' runtimeRefusal' metaObstruction'
          reflectionLimit' auditLedger' transport' routes' provenance' nameCert' =>
          cases hfields
          rfl

instance runtimeBoundaryAuditBHistCarrier :
    BHistCarrier RuntimeBoundaryAuditUp where
  toEventFlow := runtimeBoundaryAuditToEventFlow
  fromEventFlow := runtimeBoundaryAuditFromEventFlow

instance runtimeBoundaryAuditChapterTasteGate :
    ChapterTasteGate RuntimeBoundaryAuditUp where
  round_trip := by
    intro x
    change
      runtimeBoundaryAuditFromEventFlow (runtimeBoundaryAuditToEventFlow x) = some x
    exact runtimeBoundaryAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (runtimeBoundaryAuditToEventFlow_injective heq)

instance runtimeBoundaryAuditFieldFaithful :
    FieldFaithful RuntimeBoundaryAuditUp where
  fields := runtimeBoundaryAuditFields
  field_faithful := runtimeBoundaryAudit_field_faithful

instance runtimeBoundaryAuditNontrivial :
    Nontrivial RuntimeBoundaryAuditUp where
  witness_pair :=
    ⟨RuntimeBoundaryAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RuntimeBoundaryAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RuntimeBoundaryAuditUp :=
  runtimeBoundaryAuditChapterTasteGate

theorem RuntimeBoundaryAuditTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RuntimeBoundaryAuditUp) ∧
      Nonempty (FieldFaithful RuntimeBoundaryAuditUp) ∧
      Nonempty (Nontrivial RuntimeBoundaryAuditUp) ∧
        (∀ h : BHist,
          runtimeBoundaryAuditDecodeBHist (runtimeBoundaryAuditEncodeBHist h) = h) ∧
          runtimeBoundaryAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact
    ⟨⟨runtimeBoundaryAuditChapterTasteGate⟩, ⟨runtimeBoundaryAuditFieldFaithful⟩,
      ⟨runtimeBoundaryAuditNontrivial⟩, runtimeBoundaryAudit_decode_encode_bhist, rfl⟩

end BEDC.Derived.RuntimeBoundaryAuditUp
