import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedTermSubstitutionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedTermSubstitutionUp : Type where
  | mk :
      (term boundary value witness transport route provenance name : BHist) →
      ClosedTermSubstitutionUp
  deriving DecidableEq

def closedTermSubstitutionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedTermSubstitutionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedTermSubstitutionEncodeBHist h

def closedTermSubstitutionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedTermSubstitutionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedTermSubstitutionDecodeBHist tail)

private theorem closedTermSubstitutionDecode_encode_bhist :
    ∀ h : BHist,
      closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem closedTermSubstitution_mk_congr
    {term term' boundary boundary' value value' witness witness' transport transport'
      route route' provenance provenance' name name' : BHist}
    (hTerm : term' = term)
    (hBoundary : boundary' = boundary)
    (hValue : value' = value)
    (hWitness : witness' = witness)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ClosedTermSubstitutionUp.mk term' boundary' value' witness' transport' route'
        provenance' name' =
      ClosedTermSubstitutionUp.mk term boundary value witness transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTerm
  cases hBoundary
  cases hValue
  cases hWitness
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def closedTermSubstitutionToEventFlow : ClosedTermSubstitutionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedTermSubstitutionUp.mk term boundary value witness transport route provenance name =>
      [[BMark.b0],
        closedTermSubstitutionEncodeBHist term,
        [BMark.b1, BMark.b0],
        closedTermSubstitutionEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionEncodeBHist value,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedTermSubstitutionEncodeBHist name]

def closedTermSubstitutionFromEventFlow : EventFlow → Option ClosedTermSubstitutionUp
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
              | boundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | value :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | witness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ClosedTermSubstitutionUp.mk
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            term)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            boundary)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            value)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            witness)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            transport)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            route)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            provenance)
                                                                          (closedTermSubstitutionDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem closedTermSubstitution_round_trip :
    ∀ x : ClosedTermSubstitutionUp,
      closedTermSubstitutionFromEventFlow (closedTermSubstitutionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term boundary value witness transport route provenance name =>
      change
        some
          (ClosedTermSubstitutionUp.mk
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist term))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist boundary))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist value))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist witness))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist transport))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist route))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist provenance))
            (closedTermSubstitutionDecodeBHist (closedTermSubstitutionEncodeBHist name))) =
          some
            (ClosedTermSubstitutionUp.mk term boundary value witness transport route provenance
              name)
      exact
        congrArg some
          (closedTermSubstitution_mk_congr
            (closedTermSubstitutionDecode_encode_bhist term)
            (closedTermSubstitutionDecode_encode_bhist boundary)
            (closedTermSubstitutionDecode_encode_bhist value)
            (closedTermSubstitutionDecode_encode_bhist witness)
            (closedTermSubstitutionDecode_encode_bhist transport)
            (closedTermSubstitutionDecode_encode_bhist route)
            (closedTermSubstitutionDecode_encode_bhist provenance)
            (closedTermSubstitutionDecode_encode_bhist name))

private theorem closedTermSubstitutionToEventFlow_injective
    {x y : ClosedTermSubstitutionUp} :
    closedTermSubstitutionToEventFlow x = closedTermSubstitutionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedTermSubstitutionFromEventFlow (closedTermSubstitutionToEventFlow x) =
        closedTermSubstitutionFromEventFlow (closedTermSubstitutionToEventFlow y) :=
    congrArg closedTermSubstitutionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedTermSubstitution_round_trip x).symm
      (Eq.trans hread (closedTermSubstitution_round_trip y)))

instance closedTermSubstitutionBHistCarrier :
    BHistCarrier ClosedTermSubstitutionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedTermSubstitutionToEventFlow
  fromEventFlow := closedTermSubstitutionFromEventFlow

instance closedTermSubstitutionChapterTasteGate :
    ChapterTasteGate ClosedTermSubstitutionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedTermSubstitutionFromEventFlow (closedTermSubstitutionToEventFlow x) = some x
    exact closedTermSubstitution_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedTermSubstitutionToEventFlow_injective heq)

theorem ClosedTermSubstitutionTasteGate_single_carrier_alignment :
    (forall h : BHist, closedTermSubstitutionDecodeBHist
        (closedTermSubstitutionEncodeBHist h) = h) /\
      (forall x : ClosedTermSubstitutionUp, closedTermSubstitutionFromEventFlow
        (closedTermSubstitutionToEventFlow x) = some x) /\
      (forall x y : ClosedTermSubstitutionUp, closedTermSubstitutionToEventFlow x =
        closedTermSubstitutionToEventFlow y -> x = y) /\
      closedTermSubstitutionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedTermSubstitutionDecode_encode_bhist
  · constructor
    · exact closedTermSubstitution_round_trip
    · constructor
      · intro x y heq
        exact closedTermSubstitutionToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedTermSubstitutionUp
