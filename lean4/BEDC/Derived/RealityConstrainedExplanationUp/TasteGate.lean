import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedExplanationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedExplanationUp : Type where
  | mk :
      (observationBundle model phenomenon signature descent residue failure transport route
        provenance localName : BHist) →
      RealityConstrainedExplanationUp
  deriving DecidableEq

def realityConstrainedExplanationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedExplanationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedExplanationEncodeBHist h

def realityConstrainedExplanationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedExplanationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedExplanationDecodeBHist tail)

private theorem realityConstrainedExplanation_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedExplanationDecodeBHist
        (realityConstrainedExplanationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedExplanation_mk_congr
    {observationBundle observationBundle' model model' phenomenon phenomenon'
      signature signature' descent descent' residue residue' failure failure'
      transport transport' route route' provenance provenance' localName localName' : BHist}
    (hObservationBundle : observationBundle' = observationBundle)
    (hModel : model' = model)
    (hPhenomenon : phenomenon' = phenomenon)
    (hSignature : signature' = signature)
    (hDescent : descent' = descent)
    (hResidue : residue' = residue)
    (hFailure : failure' = failure)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RealityConstrainedExplanationUp.mk observationBundle' model' phenomenon' signature'
        descent' residue' failure' transport' route' provenance' localName' =
      RealityConstrainedExplanationUp.mk observationBundle model phenomenon signature descent
        residue failure transport route provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObservationBundle
  cases hModel
  cases hPhenomenon
  cases hSignature
  cases hDescent
  cases hResidue
  cases hFailure
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hLocalName
  rfl

def realityConstrainedExplanationToEventFlow : RealityConstrainedExplanationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedExplanationUp.mk observationBundle model phenomenon signature descent
      residue failure transport route provenance localName =>
      [[BMark.b0],
        realityConstrainedExplanationEncodeBHist observationBundle,
        [BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist model,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist phenomenon,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist signature,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedExplanationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedExplanationEncodeBHist localName]

def realityConstrainedExplanationFromEventFlow :
    EventFlow → Option RealityConstrainedExplanationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observationBundle :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | model :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | phenomenon :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | signature :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | descent :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | residue :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | failure :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | localName :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RealityConstrainedExplanationUp.mk
                                                                                                  (realityConstrainedExplanationDecodeBHist observationBundle)
                                                                                                  (realityConstrainedExplanationDecodeBHist model)
                                                                                                  (realityConstrainedExplanationDecodeBHist phenomenon)
                                                                                                  (realityConstrainedExplanationDecodeBHist signature)
                                                                                                  (realityConstrainedExplanationDecodeBHist descent)
                                                                                                  (realityConstrainedExplanationDecodeBHist residue)
                                                                                                  (realityConstrainedExplanationDecodeBHist failure)
                                                                                                  (realityConstrainedExplanationDecodeBHist transport)
                                                                                                  (realityConstrainedExplanationDecodeBHist route)
                                                                                                  (realityConstrainedExplanationDecodeBHist provenance)
                                                                                                  (realityConstrainedExplanationDecodeBHist localName))
                                                                                          | _ :: _ => none

private theorem realityConstrainedExplanation_round_trip :
    ∀ x : RealityConstrainedExplanationUp,
      realityConstrainedExplanationFromEventFlow
        (realityConstrainedExplanationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observationBundle model phenomenon signature descent residue failure transport route
      provenance localName =>
      change
        some
          (RealityConstrainedExplanationUp.mk
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist observationBundle))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist model))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist phenomenon))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist signature))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist descent))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist residue))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist failure))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist transport))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist route))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist provenance))
            (realityConstrainedExplanationDecodeBHist
              (realityConstrainedExplanationEncodeBHist localName))) =
          some
            (RealityConstrainedExplanationUp.mk observationBundle model phenomenon signature
              descent residue failure transport route provenance localName)
      exact
        congrArg some
          (realityConstrainedExplanation_mk_congr
            (realityConstrainedExplanation_decode_encode_bhist observationBundle)
            (realityConstrainedExplanation_decode_encode_bhist model)
            (realityConstrainedExplanation_decode_encode_bhist phenomenon)
            (realityConstrainedExplanation_decode_encode_bhist signature)
            (realityConstrainedExplanation_decode_encode_bhist descent)
            (realityConstrainedExplanation_decode_encode_bhist residue)
            (realityConstrainedExplanation_decode_encode_bhist failure)
            (realityConstrainedExplanation_decode_encode_bhist transport)
            (realityConstrainedExplanation_decode_encode_bhist route)
            (realityConstrainedExplanation_decode_encode_bhist provenance)
            (realityConstrainedExplanation_decode_encode_bhist localName))

private theorem realityConstrainedExplanationToEventFlow_injective
    {x y : RealityConstrainedExplanationUp} :
    realityConstrainedExplanationToEventFlow x =
      realityConstrainedExplanationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedExplanationFromEventFlow
          (realityConstrainedExplanationToEventFlow x) =
        realityConstrainedExplanationFromEventFlow
          (realityConstrainedExplanationToEventFlow y) :=
    congrArg realityConstrainedExplanationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedExplanation_round_trip x).symm
      (Eq.trans hread (realityConstrainedExplanation_round_trip y)))

instance realityConstrainedExplanationBHistCarrier :
    BHistCarrier RealityConstrainedExplanationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedExplanationToEventFlow
  fromEventFlow := realityConstrainedExplanationFromEventFlow

instance realityConstrainedExplanationTasteGate :
    ChapterTasteGate RealityConstrainedExplanationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedExplanationFromEventFlow
        (realityConstrainedExplanationToEventFlow x) = some x
    exact realityConstrainedExplanation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedExplanationToEventFlow_injective heq)

instance realityConstrainedExplanationFieldFaithful :
    FieldFaithful RealityConstrainedExplanationUp where
  fields
    | RealityConstrainedExplanationUp.mk observationBundle model phenomenon signature descent
        residue failure transport route provenance localName =>
        [observationBundle, model, phenomenon, signature, descent, residue, failure, transport,
          route, provenance, localName]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk observationBundle model phenomenon signature descent residue failure transport route
        provenance localName =>
        cases y with
        | mk observationBundle' model' phenomenon' signature' descent' residue' failure'
            transport' route' provenance' localName' =>
            cases hfields
            rfl

instance realityConstrainedExplanationNontrivial :
    Nontrivial RealityConstrainedExplanationUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨RealityConstrainedExplanationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedExplanationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedExplanationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RealityConstrainedExplanationTasteGate_single_carrier_alignment :
    ChapterTasteGate RealityConstrainedExplanationUp := by
  -- BEDC touchpoint anchor: BHist BMark
  infer_instance

end BEDC.Derived.RealityConstrainedExplanationUp
