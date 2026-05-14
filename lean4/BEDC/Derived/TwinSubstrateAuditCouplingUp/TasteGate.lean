import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TwinSubstrateAuditCouplingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TwinSubstrateAuditCouplingUp : Type where
  | mk
      (metaCICAudit groundCompilerAudit routeClassifier couplingLedger nonCollapseClassifier
        transport continuation provenance nameCert : BHist) :
      TwinSubstrateAuditCouplingUp
  deriving DecidableEq

private def twinSubstrateAuditCouplingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: twinSubstrateAuditCouplingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: twinSubstrateAuditCouplingEncodeBHist h

private def twinSubstrateAuditCouplingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (twinSubstrateAuditCouplingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (twinSubstrateAuditCouplingDecodeBHist tail)

private theorem twinSubstrateAuditCouplingDecode_encode_bhist :
    ∀ h : BHist,
      twinSubstrateAuditCouplingDecodeBHist
        (twinSubstrateAuditCouplingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem twinSubstrateAuditCoupling_mk_congr
    {metaCICAudit metaCICAudit' groundCompilerAudit groundCompilerAudit'
      routeClassifier routeClassifier' couplingLedger couplingLedger'
      nonCollapseClassifier nonCollapseClassifier' transport transport'
      continuation continuation' provenance provenance' nameCert nameCert' : BHist}
    (hMetaCICAudit : metaCICAudit' = metaCICAudit)
    (hGroundCompilerAudit : groundCompilerAudit' = groundCompilerAudit)
    (hRouteClassifier : routeClassifier' = routeClassifier)
    (hCouplingLedger : couplingLedger' = couplingLedger)
    (hNonCollapseClassifier : nonCollapseClassifier' = nonCollapseClassifier)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    TwinSubstrateAuditCouplingUp.mk metaCICAudit' groundCompilerAudit' routeClassifier'
        couplingLedger' nonCollapseClassifier' transport' continuation' provenance' nameCert' =
      TwinSubstrateAuditCouplingUp.mk metaCICAudit groundCompilerAudit routeClassifier
        couplingLedger nonCollapseClassifier transport continuation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetaCICAudit
  cases hGroundCompilerAudit
  cases hRouteClassifier
  cases hCouplingLedger
  cases hNonCollapseClassifier
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private def twinSubstrateAuditCouplingToEventFlow :
    TwinSubstrateAuditCouplingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateAuditCouplingUp.mk metaCICAudit groundCompilerAudit routeClassifier
      couplingLedger nonCollapseClassifier transport continuation provenance nameCert =>
      [[BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist metaCICAudit,
        [BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist groundCompilerAudit,
        [BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist routeClassifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist couplingLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist nonCollapseClassifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        twinSubstrateAuditCouplingEncodeBHist nameCert]

private def twinSubstrateAuditCouplingFromEventFlow :
    EventFlow → Option TwinSubstrateAuditCouplingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metaCICAudit :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | groundCompilerAudit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | routeClassifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | couplingLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nonCollapseClassifier :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (TwinSubstrateAuditCouplingUp.mk
                                                                                  (twinSubstrateAuditCouplingDecodeBHist metaCICAudit)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist groundCompilerAudit)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist routeClassifier)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist couplingLedger)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist nonCollapseClassifier)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist transport)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist continuation)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist provenance)
                                                                                  (twinSubstrateAuditCouplingDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem twinSubstrateAuditCoupling_round_trip :
    ∀ x : TwinSubstrateAuditCouplingUp,
      twinSubstrateAuditCouplingFromEventFlow
        (twinSubstrateAuditCouplingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metaCICAudit groundCompilerAudit routeClassifier couplingLedger
      nonCollapseClassifier transport continuation provenance nameCert =>
      change
        some
          (TwinSubstrateAuditCouplingUp.mk
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist metaCICAudit))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist groundCompilerAudit))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist routeClassifier))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist couplingLedger))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist nonCollapseClassifier))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist transport))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist continuation))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist provenance))
            (twinSubstrateAuditCouplingDecodeBHist
              (twinSubstrateAuditCouplingEncodeBHist nameCert))) =
          some
            (TwinSubstrateAuditCouplingUp.mk metaCICAudit groundCompilerAudit
              routeClassifier couplingLedger nonCollapseClassifier transport
              continuation provenance nameCert)
      exact
        congrArg some
          (twinSubstrateAuditCoupling_mk_congr
            (twinSubstrateAuditCouplingDecode_encode_bhist metaCICAudit)
            (twinSubstrateAuditCouplingDecode_encode_bhist groundCompilerAudit)
            (twinSubstrateAuditCouplingDecode_encode_bhist routeClassifier)
            (twinSubstrateAuditCouplingDecode_encode_bhist couplingLedger)
            (twinSubstrateAuditCouplingDecode_encode_bhist nonCollapseClassifier)
            (twinSubstrateAuditCouplingDecode_encode_bhist transport)
            (twinSubstrateAuditCouplingDecode_encode_bhist continuation)
            (twinSubstrateAuditCouplingDecode_encode_bhist provenance)
            (twinSubstrateAuditCouplingDecode_encode_bhist nameCert))

private theorem twinSubstrateAuditCouplingToEventFlow_injective
    {x y : TwinSubstrateAuditCouplingUp} :
    twinSubstrateAuditCouplingToEventFlow x =
      twinSubstrateAuditCouplingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      twinSubstrateAuditCouplingFromEventFlow
          (twinSubstrateAuditCouplingToEventFlow x) =
        twinSubstrateAuditCouplingFromEventFlow
          (twinSubstrateAuditCouplingToEventFlow y) :=
    congrArg twinSubstrateAuditCouplingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (twinSubstrateAuditCoupling_round_trip x).symm
      (Eq.trans hread (twinSubstrateAuditCoupling_round_trip y)))

instance twinSubstrateAuditCouplingBHistCarrier :
    BHistCarrier TwinSubstrateAuditCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := twinSubstrateAuditCouplingToEventFlow
  fromEventFlow := twinSubstrateAuditCouplingFromEventFlow

instance twinSubstrateAuditCouplingChapterTasteGate :
    ChapterTasteGate TwinSubstrateAuditCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      twinSubstrateAuditCouplingFromEventFlow
        (twinSubstrateAuditCouplingToEventFlow x) = some x
    exact twinSubstrateAuditCoupling_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (twinSubstrateAuditCouplingToEventFlow_injective heq)

instance twinSubstrateAuditCouplingFieldFaithful :
    FieldFaithful TwinSubstrateAuditCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TwinSubstrateAuditCouplingUp.mk metaCICAudit groundCompilerAudit routeClassifier
        couplingLedger nonCollapseClassifier transport continuation provenance nameCert =>
        [metaCICAudit, groundCompilerAudit, routeClassifier, couplingLedger,
          nonCollapseClassifier, transport, continuation, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk metaCICAudit groundCompilerAudit routeClassifier couplingLedger
        nonCollapseClassifier transport continuation provenance nameCert =>
        cases y with
        | mk metaCICAudit' groundCompilerAudit' routeClassifier' couplingLedger'
            nonCollapseClassifier' transport' continuation' provenance' nameCert' =>
            cases hfields
            rfl

instance twinSubstrateAuditCouplingNontrivial :
    Nontrivial TwinSubstrateAuditCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TwinSubstrateAuditCouplingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TwinSubstrateAuditCouplingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TwinSubstrateAuditCouplingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      twinSubstrateAuditCouplingDecodeBHist
        (twinSubstrateAuditCouplingEncodeBHist h) = h) ∧
      (∀ x : TwinSubstrateAuditCouplingUp,
        twinSubstrateAuditCouplingFromEventFlow
          (twinSubstrateAuditCouplingToEventFlow x) = some x) ∧
        (∀ x y : TwinSubstrateAuditCouplingUp,
          twinSubstrateAuditCouplingToEventFlow x =
            twinSubstrateAuditCouplingToEventFlow y → x = y) ∧
          twinSubstrateAuditCouplingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact twinSubstrateAuditCouplingDecode_encode_bhist
  · constructor
    · exact twinSubstrateAuditCoupling_round_trip
    · constructor
      · intro x y heq
        exact twinSubstrateAuditCouplingToEventFlow_injective heq
      · rfl

end BEDC.Derived.TwinSubstrateAuditCouplingUp
