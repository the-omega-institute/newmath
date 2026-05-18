import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSubstitutionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSubstitutionBoundaryUp : Type where
  | mk :
      (term depth payload classifier shift substitute transport route provenance name : BHist) →
        ClosedSubstitutionBoundaryUp
  deriving DecidableEq

def closedSubstitutionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSubstitutionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSubstitutionBoundaryEncodeBHist h

def closedSubstitutionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSubstitutionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSubstitutionBoundaryDecodeBHist tail)

private theorem closedSubstitutionBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      closedSubstitutionBoundaryDecodeBHist (closedSubstitutionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem closedSubstitutionBoundary_mk_congr
    {term term' depth depth' payload payload' classifier classifier' shift shift'
      substitute substitute' transport transport' route route' provenance provenance'
      name name' : BHist}
    (hTerm : term' = term)
    (hDepth : depth' = depth)
    (hPayload : payload' = payload)
    (hClassifier : classifier' = classifier)
    (hShift : shift' = shift)
    (hSubstitute : substitute' = substitute)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ClosedSubstitutionBoundaryUp.mk term' depth' payload' classifier' shift' substitute'
        transport' route' provenance' name' =
      ClosedSubstitutionBoundaryUp.mk term depth payload classifier shift substitute transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTerm
  cases hDepth
  cases hPayload
  cases hClassifier
  cases hShift
  cases hSubstitute
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def closedSubstitutionBoundaryToEventFlow : ClosedSubstitutionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSubstitutionBoundaryUp.mk term depth payload classifier shift substitute transport
      route provenance name =>
      [[BMark.b0],
        closedSubstitutionBoundaryEncodeBHist term,
        [BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist depth,
        [BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist payload,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist shift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist substitute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedSubstitutionBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionBoundaryEncodeBHist name]

def closedSubstitutionBoundaryFromEventFlow :
    EventFlow → Option ClosedSubstitutionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | depth :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | payload :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | shift :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | substitute :: rest11 =>
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
                                                              | route :: rest15 =>
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
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ClosedSubstitutionBoundaryUp.mk
                                                                                          (closedSubstitutionBoundaryDecodeBHist term)
                                                                                          (closedSubstitutionBoundaryDecodeBHist depth)
                                                                                          (closedSubstitutionBoundaryDecodeBHist payload)
                                                                                          (closedSubstitutionBoundaryDecodeBHist classifier)
                                                                                          (closedSubstitutionBoundaryDecodeBHist shift)
                                                                                          (closedSubstitutionBoundaryDecodeBHist substitute)
                                                                                          (closedSubstitutionBoundaryDecodeBHist transport)
                                                                                          (closedSubstitutionBoundaryDecodeBHist route)
                                                                                          (closedSubstitutionBoundaryDecodeBHist provenance)
                                                                                          (closedSubstitutionBoundaryDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem closedSubstitutionBoundary_round_trip :
    ∀ x : ClosedSubstitutionBoundaryUp,
      closedSubstitutionBoundaryFromEventFlow
        (closedSubstitutionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term depth payload classifier shift substitute transport route provenance name =>
      change
        some
          (ClosedSubstitutionBoundaryUp.mk
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist term))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist depth))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist payload))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist classifier))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist shift))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist substitute))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist transport))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist route))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist provenance))
            (closedSubstitutionBoundaryDecodeBHist
              (closedSubstitutionBoundaryEncodeBHist name))) =
          some
            (ClosedSubstitutionBoundaryUp.mk term depth payload classifier shift substitute
              transport route provenance name)
      exact
        congrArg some
          (closedSubstitutionBoundary_mk_congr
            (closedSubstitutionBoundaryDecode_encode_bhist term)
            (closedSubstitutionBoundaryDecode_encode_bhist depth)
            (closedSubstitutionBoundaryDecode_encode_bhist payload)
            (closedSubstitutionBoundaryDecode_encode_bhist classifier)
            (closedSubstitutionBoundaryDecode_encode_bhist shift)
            (closedSubstitutionBoundaryDecode_encode_bhist substitute)
            (closedSubstitutionBoundaryDecode_encode_bhist transport)
            (closedSubstitutionBoundaryDecode_encode_bhist route)
            (closedSubstitutionBoundaryDecode_encode_bhist provenance)
            (closedSubstitutionBoundaryDecode_encode_bhist name))

private theorem closedSubstitutionBoundaryToEventFlow_injective
    {x y : ClosedSubstitutionBoundaryUp} :
    closedSubstitutionBoundaryToEventFlow x = closedSubstitutionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedSubstitutionBoundaryFromEventFlow (closedSubstitutionBoundaryToEventFlow x) =
        closedSubstitutionBoundaryFromEventFlow (closedSubstitutionBoundaryToEventFlow y) :=
    congrArg closedSubstitutionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedSubstitutionBoundary_round_trip x).symm
      (Eq.trans hread (closedSubstitutionBoundary_round_trip y)))

instance closedSubstitutionBoundaryBHistCarrier :
    BHistCarrier ClosedSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSubstitutionBoundaryToEventFlow
  fromEventFlow := closedSubstitutionBoundaryFromEventFlow

instance closedSubstitutionBoundaryChapterTasteGate :
    ChapterTasteGate ClosedSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedSubstitutionBoundaryFromEventFlow (closedSubstitutionBoundaryToEventFlow x) =
        some x
    exact closedSubstitutionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedSubstitutionBoundaryToEventFlow_injective heq)

instance closedSubstitutionBoundaryFieldFaithful :
    FieldFaithful ClosedSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosedSubstitutionBoundaryUp.mk term depth payload classifier shift substitute transport
        route provenance name =>
        [term, depth, payload, classifier, shift, substitute, transport, route, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk term depth payload classifier shift substitute transport route provenance name =>
      cases y with
      | mk term' depth' payload' classifier' shift' substitute' transport' route' provenance'
          name' =>
          cases hfields
          rfl

def taste_gate : ChapterTasteGate ClosedSubstitutionBoundaryUp :=
  closedSubstitutionBoundaryChapterTasteGate

theorem ClosedSubstitutionBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      closedSubstitutionBoundaryDecodeBHist (closedSubstitutionBoundaryEncodeBHist h) = h) /\
      (forall x : ClosedSubstitutionBoundaryUp,
        closedSubstitutionBoundaryFromEventFlow
          (closedSubstitutionBoundaryToEventFlow x) = some x) /\
      (forall x y : ClosedSubstitutionBoundaryUp,
        closedSubstitutionBoundaryToEventFlow x = closedSubstitutionBoundaryToEventFlow y ->
          x = y) /\
      closedSubstitutionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedSubstitutionBoundaryDecode_encode_bhist
  · constructor
    · exact closedSubstitutionBoundary_round_trip
    · constructor
      · intro x y heq
        exact closedSubstitutionBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedSubstitutionBoundaryUp
