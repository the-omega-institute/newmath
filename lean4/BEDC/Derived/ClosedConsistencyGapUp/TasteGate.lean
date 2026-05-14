import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedConsistencyGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedConsistencyGapUp : Type where
  | mk :
      (audit closedNormal subjectReduction dischargeSocket typedEndpoint transport routes
        provenance localName : BHist) →
      ClosedConsistencyGapUp
  deriving DecidableEq

def closedConsistencyGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedConsistencyGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedConsistencyGapEncodeBHist h

private def closedConsistencyGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedConsistencyGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedConsistencyGapDecodeBHist tail)

private theorem closedConsistencyGapDecode_encode_bhist :
    ∀ h : BHist, closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem closedConsistencyGap_mk_congr
    {audit audit' closedNormal closedNormal' subjectReduction subjectReduction'
      dischargeSocket dischargeSocket' typedEndpoint typedEndpoint' transport transport'
      routes routes' provenance provenance' localName localName' : BHist}
    (hAudit : audit' = audit)
    (hClosedNormal : closedNormal' = closedNormal)
    (hSubjectReduction : subjectReduction' = subjectReduction)
    (hDischargeSocket : dischargeSocket' = dischargeSocket)
    (hTypedEndpoint : typedEndpoint' = typedEndpoint)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    ClosedConsistencyGapUp.mk audit' closedNormal' subjectReduction' dischargeSocket'
        typedEndpoint' transport' routes' provenance' localName' =
      ClosedConsistencyGapUp.mk audit closedNormal subjectReduction dischargeSocket typedEndpoint
        transport routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAudit
  cases hClosedNormal
  cases hSubjectReduction
  cases hDischargeSocket
  cases hTypedEndpoint
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

private def closedConsistencyGapToEventFlow : ClosedConsistencyGapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedConsistencyGapUp.mk audit closedNormal subjectReduction dischargeSocket typedEndpoint
      transport routes provenance localName =>
      [[BMark.b0],
        closedConsistencyGapEncodeBHist audit,
        [BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist closedNormal,
        [BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist subjectReduction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist dischargeSocket,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist typedEndpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedConsistencyGapEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedConsistencyGapEncodeBHist localName]

private def closedConsistencyGapFromEventFlow : EventFlow → Option ClosedConsistencyGapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | audit :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedNormal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | subjectReduction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dischargeSocket :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | typedEndpoint :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ClosedConsistencyGapUp.mk
                                                                                  (closedConsistencyGapDecodeBHist audit)
                                                                                  (closedConsistencyGapDecodeBHist closedNormal)
                                                                                  (closedConsistencyGapDecodeBHist subjectReduction)
                                                                                  (closedConsistencyGapDecodeBHist dischargeSocket)
                                                                                  (closedConsistencyGapDecodeBHist typedEndpoint)
                                                                                  (closedConsistencyGapDecodeBHist transport)
                                                                                  (closedConsistencyGapDecodeBHist routes)
                                                                                  (closedConsistencyGapDecodeBHist provenance)
                                                                                  (closedConsistencyGapDecodeBHist localName))
                                                                          | _ :: _ => none

private theorem closedConsistencyGap_round_trip :
    ∀ x : ClosedConsistencyGapUp,
      closedConsistencyGapFromEventFlow (closedConsistencyGapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk audit closedNormal subjectReduction dischargeSocket typedEndpoint transport routes
      provenance localName =>
      change
        some
          (ClosedConsistencyGapUp.mk
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist audit))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist closedNormal))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist subjectReduction))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist dischargeSocket))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist typedEndpoint))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist transport))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist routes))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist provenance))
            (closedConsistencyGapDecodeBHist (closedConsistencyGapEncodeBHist localName))) =
          some
            (ClosedConsistencyGapUp.mk audit closedNormal subjectReduction dischargeSocket
              typedEndpoint transport routes provenance localName)
      exact
        congrArg some
          (closedConsistencyGap_mk_congr
            (closedConsistencyGapDecode_encode_bhist audit)
            (closedConsistencyGapDecode_encode_bhist closedNormal)
            (closedConsistencyGapDecode_encode_bhist subjectReduction)
            (closedConsistencyGapDecode_encode_bhist dischargeSocket)
            (closedConsistencyGapDecode_encode_bhist typedEndpoint)
            (closedConsistencyGapDecode_encode_bhist transport)
            (closedConsistencyGapDecode_encode_bhist routes)
            (closedConsistencyGapDecode_encode_bhist provenance)
            (closedConsistencyGapDecode_encode_bhist localName))

private theorem closedConsistencyGapToEventFlow_injective {x y : ClosedConsistencyGapUp} :
    closedConsistencyGapToEventFlow x = closedConsistencyGapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedConsistencyGapFromEventFlow (closedConsistencyGapToEventFlow x) =
        closedConsistencyGapFromEventFlow (closedConsistencyGapToEventFlow y) :=
    congrArg closedConsistencyGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedConsistencyGap_round_trip x).symm
      (Eq.trans hread (closedConsistencyGap_round_trip y)))

instance closedConsistencyGapBHistCarrier : BHistCarrier ClosedConsistencyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedConsistencyGapToEventFlow
  fromEventFlow := closedConsistencyGapFromEventFlow

instance closedConsistencyGapChapterTasteGate : ChapterTasteGate ClosedConsistencyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedConsistencyGapFromEventFlow (closedConsistencyGapToEventFlow x) = some x
    exact closedConsistencyGap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedConsistencyGapToEventFlow_injective heq)

instance closedConsistencyGapFieldFaithful : FieldFaithful ClosedConsistencyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosedConsistencyGapUp.mk audit closedNormal subjectReduction dischargeSocket typedEndpoint
        transport routes provenance localName =>
        [audit, closedNormal, subjectReduction, dischargeSocket, typedEndpoint, transport, routes,
          provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk audit₁ closedNormal₁ subjectReduction₁ dischargeSocket₁ typedEndpoint₁ transport₁
        routes₁ provenance₁ localName₁ =>
      cases y with
      | mk audit₂ closedNormal₂ subjectReduction₂ dischargeSocket₂ typedEndpoint₂ transport₂
          routes₂ provenance₂ localName₂ =>
        injection h with hAudit t1
        injection t1 with hClosedNormal t2
        injection t2 with hSubjectReduction t3
        injection t3 with hDischargeSocket t4
        injection t4 with hTypedEndpoint t5
        injection t5 with hTransport t6
        injection t6 with hRoutes t7
        injection t7 with hProvenance t8
        injection t8 with hLocalName _
        cases hAudit
        cases hClosedNormal
        cases hSubjectReduction
        cases hDischargeSocket
        cases hTypedEndpoint
        cases hTransport
        cases hRoutes
        cases hProvenance
        cases hLocalName
        rfl

theorem ClosedConsistencyGapTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ClosedConsistencyGapUp) ∧
      Nonempty (ChapterTasteGate ClosedConsistencyGapUp) ∧
        closedConsistencyGapEncodeBHist BHist.Empty = ([] : RawEvent) ∧
          closedConsistencyGapEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨closedConsistencyGapBHistCarrier⟩
  · constructor
    · exact ⟨closedConsistencyGapChapterTasteGate⟩
    · constructor
      · rfl
      · rfl

end BEDC.Derived.ClosedConsistencyGapUp
