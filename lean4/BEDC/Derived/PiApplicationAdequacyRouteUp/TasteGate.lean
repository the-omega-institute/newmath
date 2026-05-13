import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PiApplicationAdequacyRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PiApplicationAdequacyRouteUp : Type where
  | mk :
      (functionEvidence argumentEvidence applicationCandidate typedApplication stepSN
        noInfinite route name provenance transport query : BHist) →
      PiApplicationAdequacyRouteUp
  deriving DecidableEq

def piApplicationAdequacyRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: piApplicationAdequacyRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: piApplicationAdequacyRouteEncodeBHist h

def piApplicationAdequacyRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (piApplicationAdequacyRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (piApplicationAdequacyRouteDecodeBHist tail)

private theorem piApplicationAdequacyRoute_decode_encode_bhist :
    ∀ h : BHist,
      piApplicationAdequacyRouteDecodeBHist
        (piApplicationAdequacyRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def piApplicationAdequacyRouteToEventFlow :
    PiApplicationAdequacyRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PiApplicationAdequacyRouteUp.mk functionEvidence argumentEvidence
      applicationCandidate typedApplication stepSN noInfinite route name provenance
      transport query =>
      [[BMark.b0],
        piApplicationAdequacyRouteEncodeBHist functionEvidence,
        [BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist argumentEvidence,
        [BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist applicationCandidate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist typedApplication,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist stepSN,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist noInfinite,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        piApplicationAdequacyRouteEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        piApplicationAdequacyRouteEncodeBHist query]

def piApplicationAdequacyRouteFromEventFlow :
    EventFlow → Option PiApplicationAdequacyRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | functionEvidence :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | argumentEvidence :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | applicationCandidate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | typedApplication :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | stepSN :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | noInfinite :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
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
                                                                              | transport :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | query :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (PiApplicationAdequacyRouteUp.mk
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    functionEvidence)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    argumentEvidence)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    applicationCandidate)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    typedApplication)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    stepSN)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    noInfinite)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    route)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    name)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    provenance)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    transport)
                                                                                                  (piApplicationAdequacyRouteDecodeBHist
                                                                                                    query))
                                                                                          | _ :: _ => none

private theorem piApplicationAdequacyRoute_round_trip :
    ∀ x : PiApplicationAdequacyRouteUp,
      piApplicationAdequacyRouteFromEventFlow
        (piApplicationAdequacyRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk functionEvidence argumentEvidence applicationCandidate typedApplication stepSN
      noInfinite route name provenance transport query =>
      change
        some
          (PiApplicationAdequacyRouteUp.mk
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist functionEvidence))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist argumentEvidence))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist applicationCandidate))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist typedApplication))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist stepSN))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist noInfinite))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist route))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist name))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist provenance))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist transport))
            (piApplicationAdequacyRouteDecodeBHist
              (piApplicationAdequacyRouteEncodeBHist query))) =
          some
            (PiApplicationAdequacyRouteUp.mk functionEvidence argumentEvidence
              applicationCandidate typedApplication stepSN noInfinite route name
              provenance transport query)
      rw [piApplicationAdequacyRoute_decode_encode_bhist functionEvidence,
        piApplicationAdequacyRoute_decode_encode_bhist argumentEvidence,
        piApplicationAdequacyRoute_decode_encode_bhist applicationCandidate,
        piApplicationAdequacyRoute_decode_encode_bhist typedApplication,
        piApplicationAdequacyRoute_decode_encode_bhist stepSN,
        piApplicationAdequacyRoute_decode_encode_bhist noInfinite,
        piApplicationAdequacyRoute_decode_encode_bhist route,
        piApplicationAdequacyRoute_decode_encode_bhist name,
        piApplicationAdequacyRoute_decode_encode_bhist provenance,
        piApplicationAdequacyRoute_decode_encode_bhist transport,
        piApplicationAdequacyRoute_decode_encode_bhist query]

private theorem piApplicationAdequacyRouteToEventFlow_injective
    {x y : PiApplicationAdequacyRouteUp} :
    piApplicationAdequacyRouteToEventFlow x =
      piApplicationAdequacyRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      piApplicationAdequacyRouteFromEventFlow
          (piApplicationAdequacyRouteToEventFlow x) =
        piApplicationAdequacyRouteFromEventFlow
          (piApplicationAdequacyRouteToEventFlow y) :=
    congrArg piApplicationAdequacyRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (piApplicationAdequacyRoute_round_trip x).symm
      (Eq.trans hread (piApplicationAdequacyRoute_round_trip y)))

instance piApplicationAdequacyRouteBHistCarrier :
    BHistCarrier PiApplicationAdequacyRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := piApplicationAdequacyRouteToEventFlow
  fromEventFlow := piApplicationAdequacyRouteFromEventFlow

instance piApplicationAdequacyRouteChapterTasteGate :
    ChapterTasteGate PiApplicationAdequacyRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      piApplicationAdequacyRouteFromEventFlow
        (piApplicationAdequacyRouteToEventFlow x) = some x
    exact piApplicationAdequacyRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (piApplicationAdequacyRouteToEventFlow_injective heq)

instance piApplicationAdequacyRouteNontrivial :
    Nontrivial PiApplicationAdequacyRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PiApplicationAdequacyRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      PiApplicationAdequacyRouteUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance piApplicationAdequacyRouteFieldFaithful :
    FieldFaithful PiApplicationAdequacyRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PiApplicationAdequacyRouteUp.mk functionEvidence argumentEvidence
        applicationCandidate typedApplication stepSN noInfinite route name provenance
        transport query =>
        [functionEvidence, argumentEvidence, applicationCandidate, typedApplication,
          stepSN, noInfinite, route, name, provenance, transport, query]
  field_faithful := by
    intro x y h
    cases x with
    | mk functionEvidence argumentEvidence applicationCandidate typedApplication stepSN
        noInfinite route name provenance transport query =>
        cases y with
        | mk functionEvidence' argumentEvidence' applicationCandidate' typedApplication'
            stepSN' noInfinite' route' name' provenance' transport' query' =>
            cases h
            rfl

theorem PiApplicationAdequacyRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      piApplicationAdequacyRouteDecodeBHist
        (piApplicationAdequacyRouteEncodeBHist h) = h) ∧
      (∀ x : PiApplicationAdequacyRouteUp,
        piApplicationAdequacyRouteFromEventFlow
          (piApplicationAdequacyRouteToEventFlow x) = some x) ∧
        (∀ x y : PiApplicationAdequacyRouteUp,
          piApplicationAdequacyRouteToEventFlow x =
            piApplicationAdequacyRouteToEventFlow y → x = y) ∧
          piApplicationAdequacyRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact piApplicationAdequacyRoute_decode_encode_bhist
  · constructor
    · exact piApplicationAdequacyRoute_round_trip
    · constructor
      · intro x y heq
        exact piApplicationAdequacyRouteToEventFlow_injective heq
      · rfl

end BEDC.Derived.PiApplicationAdequacyRouteUp
