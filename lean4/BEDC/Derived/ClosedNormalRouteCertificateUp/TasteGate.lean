import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalRouteCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalRouteCertificateUp : Type where
  | mk :
      (mainEndpoint normalFalse obstruction candidateRoute route transport continuation
        provenance name : BHist) →
      ClosedNormalRouteCertificateUp
  deriving DecidableEq

def closedNormalRouteCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalRouteCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalRouteCertificateEncodeBHist h

def closedNormalRouteCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalRouteCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalRouteCertificateDecodeBHist tail)

private theorem closedNormalRouteCertificate_decode_encode_bhist :
    ∀ h : BHist,
      closedNormalRouteCertificateDecodeBHist (closedNormalRouteCertificateEncodeBHist h) =
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

def closedNormalRouteCertificateToEventFlow :
    ClosedNormalRouteCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalRouteCertificateUp.mk mainEndpoint normalFalse obstruction candidateRoute
      route transport continuation provenance name =>
      [[BMark.b0],
        closedNormalRouteCertificateEncodeBHist mainEndpoint,
        [BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist normalFalse,
        [BMark.b1, BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist candidateRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedNormalRouteCertificateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedNormalRouteCertificateEncodeBHist name]

def closedNormalRouteCertificateFromEventFlow :
    EventFlow → Option ClosedNormalRouteCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | mainEndpoint :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | normalFalse :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | obstruction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | candidateRoute :: rest7 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ClosedNormalRouteCertificateUp.mk
                                                                                  (closedNormalRouteCertificateDecodeBHist mainEndpoint)
                                                                                  (closedNormalRouteCertificateDecodeBHist normalFalse)
                                                                                  (closedNormalRouteCertificateDecodeBHist obstruction)
                                                                                  (closedNormalRouteCertificateDecodeBHist candidateRoute)
                                                                                  (closedNormalRouteCertificateDecodeBHist route)
                                                                                  (closedNormalRouteCertificateDecodeBHist transport)
                                                                                  (closedNormalRouteCertificateDecodeBHist continuation)
                                                                                  (closedNormalRouteCertificateDecodeBHist provenance)
                                                                                  (closedNormalRouteCertificateDecodeBHist name))
                                                                          | _ :: _ => none

private theorem closedNormalRouteCertificate_round_trip :
    ∀ x : ClosedNormalRouteCertificateUp,
      closedNormalRouteCertificateFromEventFlow
        (closedNormalRouteCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk mainEndpoint normalFalse obstruction candidateRoute route transport continuation
      provenance name =>
      change
        some
          (ClosedNormalRouteCertificateUp.mk
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist mainEndpoint))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist normalFalse))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist obstruction))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist candidateRoute))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist route))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist transport))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist continuation))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist provenance))
            (closedNormalRouteCertificateDecodeBHist
              (closedNormalRouteCertificateEncodeBHist name))) =
          some
            (ClosedNormalRouteCertificateUp.mk mainEndpoint normalFalse obstruction
              candidateRoute route transport continuation provenance name)
      rw [closedNormalRouteCertificate_decode_encode_bhist mainEndpoint,
        closedNormalRouteCertificate_decode_encode_bhist normalFalse,
        closedNormalRouteCertificate_decode_encode_bhist obstruction,
        closedNormalRouteCertificate_decode_encode_bhist candidateRoute,
        closedNormalRouteCertificate_decode_encode_bhist route,
        closedNormalRouteCertificate_decode_encode_bhist transport,
        closedNormalRouteCertificate_decode_encode_bhist continuation,
        closedNormalRouteCertificate_decode_encode_bhist provenance,
        closedNormalRouteCertificate_decode_encode_bhist name]

private theorem closedNormalRouteCertificateToEventFlow_injective
    {x y : ClosedNormalRouteCertificateUp} :
    closedNormalRouteCertificateToEventFlow x =
      closedNormalRouteCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalRouteCertificateFromEventFlow
          (closedNormalRouteCertificateToEventFlow x) =
        closedNormalRouteCertificateFromEventFlow
          (closedNormalRouteCertificateToEventFlow y) :=
    congrArg closedNormalRouteCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedNormalRouteCertificate_round_trip x).symm
      (Eq.trans hread (closedNormalRouteCertificate_round_trip y)))

instance closedNormalRouteCertificateBHistCarrier :
    BHistCarrier ClosedNormalRouteCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalRouteCertificateToEventFlow
  fromEventFlow := closedNormalRouteCertificateFromEventFlow

instance closedNormalRouteCertificateChapterTasteGate :
    ChapterTasteGate ClosedNormalRouteCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalRouteCertificateFromEventFlow
          (closedNormalRouteCertificateToEventFlow x) =
        some x
    exact closedNormalRouteCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedNormalRouteCertificateToEventFlow_injective heq)

instance closedNormalRouteCertificateFieldFaithful :
    FieldFaithful ClosedNormalRouteCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosedNormalRouteCertificateUp.mk mainEndpoint normalFalse obstruction
        candidateRoute route transport continuation provenance name =>
        [mainEndpoint, normalFalse, obstruction, candidateRoute, route, transport,
          continuation, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk mainEndpoint1 normalFalse1 obstruction1 candidateRoute1 route1 transport1
        continuation1 provenance1 name1 =>
        cases y with
        | mk mainEndpoint2 normalFalse2 obstruction2 candidateRoute2 route2 transport2
            continuation2 provenance2 name2 =>
            injection h with hMain t1
            injection t1 with hNormal t2
            injection t2 with hObstruction t3
            injection t3 with hCandidate t4
            injection t4 with hRoute t5
            injection t5 with hTransport t6
            injection t6 with hContinuation t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hMain
            cases hNormal
            cases hObstruction
            cases hCandidate
            cases hRoute
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hName
            rfl

theorem ClosedNormalRouteCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedNormalRouteCertificateDecodeBHist
        (closedNormalRouteCertificateEncodeBHist h) = h) ∧
      (∀ x : ClosedNormalRouteCertificateUp,
        closedNormalRouteCertificateFromEventFlow
          (closedNormalRouteCertificateToEventFlow x) = some x) ∧
        (∀ x y : ClosedNormalRouteCertificateUp,
          closedNormalRouteCertificateToEventFlow x =
            closedNormalRouteCertificateToEventFlow y → x = y) ∧
          closedNormalRouteCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedNormalRouteCertificate_decode_encode_bhist
  · constructor
    · exact closedNormalRouteCertificate_round_trip
    · constructor
      · intro x y heq
        exact closedNormalRouteCertificateToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedNormalRouteCertificateUp
