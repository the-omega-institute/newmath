import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionEventReplayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionEventReplayUp : Type where
  | mk
      (gap namedRecord acceptedRoute checkerReplay auditReadback transport continuation
        provenance nameCert : BHist) :
      InscriptionEventReplayUp
  deriving DecidableEq

private def inscriptionEventReplayEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionEventReplayEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionEventReplayEncodeBHist h

private def inscriptionEventReplayDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionEventReplayDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionEventReplayDecodeBHist tail)

private theorem inscriptionEventReplayDecode_encode_bhist :
    ∀ h : BHist,
      inscriptionEventReplayDecodeBHist
        (inscriptionEventReplayEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inscriptionEventReplay_mk_congr
    {gap gap' namedRecord namedRecord' acceptedRoute acceptedRoute'
      checkerReplay checkerReplay' auditReadback auditReadback' transport transport'
      continuation continuation' provenance provenance' nameCert nameCert' : BHist}
    (hGap : gap' = gap)
    (hNamedRecord : namedRecord' = namedRecord)
    (hAcceptedRoute : acceptedRoute' = acceptedRoute)
    (hCheckerReplay : checkerReplay' = checkerReplay)
    (hAuditReadback : auditReadback' = auditReadback)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    InscriptionEventReplayUp.mk gap' namedRecord' acceptedRoute' checkerReplay'
        auditReadback' transport' continuation' provenance' nameCert' =
      InscriptionEventReplayUp.mk gap namedRecord acceptedRoute checkerReplay
        auditReadback transport continuation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGap
  cases hNamedRecord
  cases hAcceptedRoute
  cases hCheckerReplay
  cases hAuditReadback
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private def inscriptionEventReplayToEventFlow :
    InscriptionEventReplayUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionEventReplayUp.mk gap namedRecord acceptedRoute checkerReplay
      auditReadback transport continuation provenance nameCert =>
      [[BMark.b0],
        inscriptionEventReplayEncodeBHist gap,
        [BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist namedRecord,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist acceptedRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist checkerReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist auditReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionEventReplayEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionEventReplayEncodeBHist nameCert]

private def inscriptionEventReplayFromEventFlow :
    EventFlow → Option InscriptionEventReplayUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gap :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | namedRecord :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | acceptedRoute :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | checkerReplay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | auditReadback :: rest9 =>
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
                                                                                (InscriptionEventReplayUp.mk
                                                                                  (inscriptionEventReplayDecodeBHist gap)
                                                                                  (inscriptionEventReplayDecodeBHist namedRecord)
                                                                                  (inscriptionEventReplayDecodeBHist acceptedRoute)
                                                                                  (inscriptionEventReplayDecodeBHist checkerReplay)
                                                                                  (inscriptionEventReplayDecodeBHist auditReadback)
                                                                                  (inscriptionEventReplayDecodeBHist transport)
                                                                                  (inscriptionEventReplayDecodeBHist continuation)
                                                                                  (inscriptionEventReplayDecodeBHist provenance)
                                                                                  (inscriptionEventReplayDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem inscriptionEventReplay_round_trip :
    ∀ x : InscriptionEventReplayUp,
      inscriptionEventReplayFromEventFlow
        (inscriptionEventReplayToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gap namedRecord acceptedRoute checkerReplay auditReadback transport continuation
      provenance nameCert =>
      change
        some
          (InscriptionEventReplayUp.mk
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist gap))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist namedRecord))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist acceptedRoute))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist checkerReplay))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist auditReadback))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist transport))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist continuation))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist provenance))
            (inscriptionEventReplayDecodeBHist
              (inscriptionEventReplayEncodeBHist nameCert))) =
          some
            (InscriptionEventReplayUp.mk gap namedRecord acceptedRoute checkerReplay
              auditReadback transport continuation provenance nameCert)
      exact
        congrArg some
          (inscriptionEventReplay_mk_congr
            (inscriptionEventReplayDecode_encode_bhist gap)
            (inscriptionEventReplayDecode_encode_bhist namedRecord)
            (inscriptionEventReplayDecode_encode_bhist acceptedRoute)
            (inscriptionEventReplayDecode_encode_bhist checkerReplay)
            (inscriptionEventReplayDecode_encode_bhist auditReadback)
            (inscriptionEventReplayDecode_encode_bhist transport)
            (inscriptionEventReplayDecode_encode_bhist continuation)
            (inscriptionEventReplayDecode_encode_bhist provenance)
            (inscriptionEventReplayDecode_encode_bhist nameCert))

private theorem inscriptionEventReplayToEventFlow_injective
    {x y : InscriptionEventReplayUp} :
    inscriptionEventReplayToEventFlow x =
      inscriptionEventReplayToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionEventReplayFromEventFlow
          (inscriptionEventReplayToEventFlow x) =
        inscriptionEventReplayFromEventFlow
          (inscriptionEventReplayToEventFlow y) :=
    congrArg inscriptionEventReplayFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionEventReplay_round_trip x).symm
      (Eq.trans hread (inscriptionEventReplay_round_trip y)))

instance inscriptionEventReplayBHistCarrier :
    BHistCarrier InscriptionEventReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionEventReplayToEventFlow
  fromEventFlow := inscriptionEventReplayFromEventFlow

instance inscriptionEventReplayChapterTasteGate :
    ChapterTasteGate InscriptionEventReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inscriptionEventReplayFromEventFlow
        (inscriptionEventReplayToEventFlow x) = some x
    exact inscriptionEventReplay_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionEventReplayToEventFlow_injective heq)

def taste_gate : ChapterTasteGate InscriptionEventReplayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inscriptionEventReplayChapterTasteGate

instance inscriptionEventReplayFieldFaithful :
    FieldFaithful InscriptionEventReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | InscriptionEventReplayUp.mk gap namedRecord acceptedRoute checkerReplay
        auditReadback transport continuation provenance nameCert =>
        [gap, namedRecord, acceptedRoute, checkerReplay, auditReadback, transport,
          continuation, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk gap namedRecord acceptedRoute checkerReplay auditReadback transport continuation
        provenance nameCert =>
        cases y with
        | mk gap' namedRecord' acceptedRoute' checkerReplay' auditReadback' transport'
            continuation' provenance' nameCert' =>
            cases hfields
            rfl

instance inscriptionEventReplayNontrivial :
    Nontrivial InscriptionEventReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InscriptionEventReplayUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionEventReplayUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem InscriptionEventReplayTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionEventReplayDecodeBHist
        (inscriptionEventReplayEncodeBHist h) = h) ∧
      (∀ x : InscriptionEventReplayUp,
        inscriptionEventReplayFromEventFlow
          (inscriptionEventReplayToEventFlow x) = some x) ∧
        (∀ x y : InscriptionEventReplayUp,
          inscriptionEventReplayToEventFlow x =
            inscriptionEventReplayToEventFlow y → x = y) ∧
          inscriptionEventReplayEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionEventReplayDecode_encode_bhist
  · constructor
    · exact inscriptionEventReplay_round_trip
    · constructor
      · intro x y heq
        exact inscriptionEventReplayToEventFlow_injective heq
      · rfl

end BEDC.Derived.InscriptionEventReplayUp
