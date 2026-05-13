import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionDischargeLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionDischargeLedgerUp : Type where
  | mk :
      (beta appArg lambdaDomain piDomain route transport replay provenance name : BHist) →
      SubjectReductionDischargeLedgerUp
  deriving DecidableEq

def subjectReductionDischargeLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionDischargeLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionDischargeLedgerEncodeBHist h

def subjectReductionDischargeLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionDischargeLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionDischargeLedgerDecodeBHist tail)

private theorem subjectReductionDischargeLedger_decode_encode_bhist :
    ∀ h : BHist,
      subjectReductionDischargeLedgerDecodeBHist
          (subjectReductionDischargeLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subjectReductionDischargeLedgerToEventFlow :
    SubjectReductionDischargeLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionDischargeLedgerUp.mk beta appArg lambdaDomain piDomain route transport
      replay provenance name =>
      [[BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist beta,
        [BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist appArg,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist lambdaDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist piDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subjectReductionDischargeLedgerEncodeBHist name]

def subjectReductionDischargeLedgerFromEventFlow :
    EventFlow → Option SubjectReductionDischargeLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | beta :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | appArg :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lambdaDomain :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | piDomain :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
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
                                                      | replay :: rest13 =>
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
                                                                      | name ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              some
                                                                                (SubjectReductionDischargeLedgerUp.mk
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    beta)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    appArg)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    lambdaDomain)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    piDomain)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    route)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    transport)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    replay)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    provenance)
                                                                                  (subjectReductionDischargeLedgerDecodeBHist
                                                                                    name))
                                                                          | _ :: _ =>
                                                                              none

private theorem subjectReductionDischargeLedger_round_trip :
    ∀ x : SubjectReductionDischargeLedgerUp,
      subjectReductionDischargeLedgerFromEventFlow
          (subjectReductionDischargeLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk beta appArg lambdaDomain piDomain route transport replay provenance name =>
      change
        some
          (SubjectReductionDischargeLedgerUp.mk
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist beta))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist appArg))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist lambdaDomain))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist piDomain))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist route))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist transport))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist replay))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist provenance))
            (subjectReductionDischargeLedgerDecodeBHist
              (subjectReductionDischargeLedgerEncodeBHist name))) =
          some
            (SubjectReductionDischargeLedgerUp.mk beta appArg lambdaDomain piDomain route
              transport replay provenance name)
      rw [subjectReductionDischargeLedger_decode_encode_bhist beta,
        subjectReductionDischargeLedger_decode_encode_bhist appArg,
        subjectReductionDischargeLedger_decode_encode_bhist lambdaDomain,
        subjectReductionDischargeLedger_decode_encode_bhist piDomain,
        subjectReductionDischargeLedger_decode_encode_bhist route,
        subjectReductionDischargeLedger_decode_encode_bhist transport,
        subjectReductionDischargeLedger_decode_encode_bhist replay,
        subjectReductionDischargeLedger_decode_encode_bhist provenance,
        subjectReductionDischargeLedger_decode_encode_bhist name]

private theorem subjectReductionDischargeLedgerToEventFlow_injective
    {x y : SubjectReductionDischargeLedgerUp} :
    subjectReductionDischargeLedgerToEventFlow x =
        subjectReductionDischargeLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionDischargeLedgerFromEventFlow
          (subjectReductionDischargeLedgerToEventFlow x) =
        subjectReductionDischargeLedgerFromEventFlow
          (subjectReductionDischargeLedgerToEventFlow y) :=
    congrArg subjectReductionDischargeLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionDischargeLedger_round_trip x).symm
      (Eq.trans hread (subjectReductionDischargeLedger_round_trip y)))

instance subjectReductionDischargeLedgerBHistCarrier :
    BHistCarrier SubjectReductionDischargeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionDischargeLedgerToEventFlow
  fromEventFlow := subjectReductionDischargeLedgerFromEventFlow

instance subjectReductionDischargeLedgerChapterTasteGate :
    ChapterTasteGate SubjectReductionDischargeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionDischargeLedgerFromEventFlow
          (subjectReductionDischargeLedgerToEventFlow x) =
        some x
    exact subjectReductionDischargeLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionDischargeLedgerToEventFlow_injective heq)

instance subjectReductionDischargeLedgerFieldFaithful :
    FieldFaithful SubjectReductionDischargeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubjectReductionDischargeLedgerUp.mk beta appArg lambdaDomain piDomain route transport
        replay provenance name =>
        [beta, appArg, lambdaDomain, piDomain, route, transport, replay, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk beta1 appArg1 lambdaDomain1 piDomain1 route1 transport1 replay1 provenance1
        name1 =>
        cases y with
        | mk beta2 appArg2 lambdaDomain2 piDomain2 route2 transport2 replay2 provenance2
            name2 =>
            injection h with hBeta t1
            injection t1 with hAppArg t2
            injection t2 with hLambdaDomain t3
            injection t3 with hPiDomain t4
            injection t4 with hRoute t5
            injection t5 with hTransport t6
            injection t6 with hReplay t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hBeta
            cases hAppArg
            cases hLambdaDomain
            cases hPiDomain
            cases hRoute
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

theorem SubjectReductionDischargeLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      subjectReductionDischargeLedgerDecodeBHist
          (subjectReductionDischargeLedgerEncodeBHist h) =
        h) ∧
      (∀ x : SubjectReductionDischargeLedgerUp,
        subjectReductionDischargeLedgerFromEventFlow
            (subjectReductionDischargeLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : SubjectReductionDischargeLedgerUp,
          subjectReductionDischargeLedgerToEventFlow x =
              subjectReductionDischargeLedgerToEventFlow y →
            x = y) ∧
          subjectReductionDischargeLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subjectReductionDischargeLedger_decode_encode_bhist
  · constructor
    · exact subjectReductionDischargeLedger_round_trip
    · constructor
      · intro x y heq
        exact subjectReductionDischargeLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubjectReductionDischargeLedgerUp
