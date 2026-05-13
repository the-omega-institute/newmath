import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionRouteUp : Type where
  | mk :
      (beta application lambda pi bundle setup invocation consumer transport route
        provenance name : BHist) →
      SubjectReductionRouteUp
  deriving DecidableEq

def subjectReductionRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionRouteEncodeBHist h

def subjectReductionRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionRouteDecodeBHist tail)

private theorem subjectReductionRoute_decode_encode_bhist :
    ∀ h : BHist,
      subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subjectReductionRouteToEventFlow : SubjectReductionRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionRouteUp.mk beta application lambda pi bundle setup invocation consumer
      transport route provenance name =>
      [[BMark.b0],
        subjectReductionRouteEncodeBHist beta,
        [BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist application,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist lambda,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist pi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist bundle,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist setup,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist invocation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionRouteEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteEncodeBHist name]

def subjectReductionRouteFromEventFlow :
    EventFlow → Option SubjectReductionRouteUp
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
              | application :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lambda :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | pi :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | bundle :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | setup :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | invocation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | consumer :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | route :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | name :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (SubjectReductionRouteUp.mk
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            beta)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            application)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            lambda)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            pi)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            bundle)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            setup)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            invocation)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            consumer)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            transport)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            route)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            provenance)
                                                                                                          (subjectReductionRouteDecodeBHist
                                                                                                            name))
                                                                                                  | _ :: _ => none

private theorem subjectReductionRoute_round_trip :
    ∀ x : SubjectReductionRouteUp,
      subjectReductionRouteFromEventFlow (subjectReductionRouteToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk beta application lambda pi bundle setup invocation consumer transport route
      provenance name =>
      change
        some
          (SubjectReductionRouteUp.mk
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist beta))
            (subjectReductionRouteDecodeBHist
              (subjectReductionRouteEncodeBHist application))
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist lambda))
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist pi))
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist bundle))
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist setup))
            (subjectReductionRouteDecodeBHist
              (subjectReductionRouteEncodeBHist invocation))
            (subjectReductionRouteDecodeBHist
              (subjectReductionRouteEncodeBHist consumer))
            (subjectReductionRouteDecodeBHist
              (subjectReductionRouteEncodeBHist transport))
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist route))
            (subjectReductionRouteDecodeBHist
              (subjectReductionRouteEncodeBHist provenance))
            (subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist name))) =
          some
            (SubjectReductionRouteUp.mk beta application lambda pi bundle setup invocation
              consumer transport route provenance name)
      rw [subjectReductionRoute_decode_encode_bhist beta,
        subjectReductionRoute_decode_encode_bhist application,
        subjectReductionRoute_decode_encode_bhist lambda,
        subjectReductionRoute_decode_encode_bhist pi,
        subjectReductionRoute_decode_encode_bhist bundle,
        subjectReductionRoute_decode_encode_bhist setup,
        subjectReductionRoute_decode_encode_bhist invocation,
        subjectReductionRoute_decode_encode_bhist consumer,
        subjectReductionRoute_decode_encode_bhist transport,
        subjectReductionRoute_decode_encode_bhist route,
        subjectReductionRoute_decode_encode_bhist provenance,
        subjectReductionRoute_decode_encode_bhist name]

private theorem subjectReductionRouteToEventFlow_injective
    {x y : SubjectReductionRouteUp} :
    subjectReductionRouteToEventFlow x = subjectReductionRouteToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionRouteFromEventFlow (subjectReductionRouteToEventFlow x) =
        subjectReductionRouteFromEventFlow (subjectReductionRouteToEventFlow y) :=
    congrArg subjectReductionRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionRoute_round_trip x).symm
      (Eq.trans hread (subjectReductionRoute_round_trip y)))

instance subjectReductionRouteBHistCarrier :
    BHistCarrier SubjectReductionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionRouteToEventFlow
  fromEventFlow := subjectReductionRouteFromEventFlow

instance subjectReductionRouteChapterTasteGate :
    ChapterTasteGate SubjectReductionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionRouteFromEventFlow (subjectReductionRouteToEventFlow x) =
        some x
    exact subjectReductionRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionRouteToEventFlow_injective heq)

instance subjectReductionRouteFieldFaithful :
    FieldFaithful SubjectReductionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubjectReductionRouteUp.mk beta application lambda pi bundle setup invocation
        consumer transport route provenance name =>
        [beta, application, lambda, pi, bundle, setup, invocation, consumer,
          transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk beta1 application1 lambda1 pi1 bundle1 setup1 invocation1 consumer1
        transport1 route1 provenance1 name1 =>
        cases y with
        | mk beta2 application2 lambda2 pi2 bundle2 setup2 invocation2 consumer2
            transport2 route2 provenance2 name2 =>
            injection h with hBeta t1
            injection t1 with hApplication t2
            injection t2 with hLambda t3
            injection t3 with hPi t4
            injection t4 with hBundle t5
            injection t5 with hSetup t6
            injection t6 with hInvocation t7
            injection t7 with hConsumer t8
            injection t8 with hTransport t9
            injection t9 with hRoute t10
            injection t10 with hProvenance t11
            injection t11 with hName _
            cases hBeta
            cases hApplication
            cases hLambda
            cases hPi
            cases hBundle
            cases hSetup
            cases hInvocation
            cases hConsumer
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem SubjectReductionRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      subjectReductionRouteDecodeBHist (subjectReductionRouteEncodeBHist h) = h) ∧
      (∀ x : SubjectReductionRouteUp,
        subjectReductionRouteFromEventFlow (subjectReductionRouteToEventFlow x) =
          some x) ∧
        (∀ x y : SubjectReductionRouteUp,
          subjectReductionRouteToEventFlow x = subjectReductionRouteToEventFlow y →
            x = y) ∧
          subjectReductionRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subjectReductionRoute_decode_encode_bhist
  · constructor
    · exact subjectReductionRoute_round_trip
    · constructor
      · intro x y heq
        exact subjectReductionRouteToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubjectReductionRouteUp
