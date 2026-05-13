import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RussellSelfMembershipBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RussellSelfMembershipBoundaryUp : Type where
  | mk :
      (contextSource selfQuery rejection stratification provenance transport route package name :
        BHist) →
        RussellSelfMembershipBoundaryUp
  deriving DecidableEq

def russellSelfMembershipBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: russellSelfMembershipBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: russellSelfMembershipBoundaryEncodeBHist h

def russellSelfMembershipBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (russellSelfMembershipBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (russellSelfMembershipBoundaryDecodeBHist tail)

private theorem russellSelfMembershipBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      russellSelfMembershipBoundaryDecodeBHist
        (russellSelfMembershipBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem russellSelfMembershipBoundary_mk_congr
    {contextSource contextSource' selfQuery selfQuery' rejection rejection'
      stratification stratification' provenance provenance' transport transport' route route'
      package package' name name' : BHist}
    (hContextSource : contextSource' = contextSource)
    (hSelfQuery : selfQuery' = selfQuery)
    (hRejection : rejection' = rejection)
    (hStratification : stratification' = stratification)
    (hProvenance : provenance' = provenance)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hPackage : package' = package)
    (hName : name' = name) :
    RussellSelfMembershipBoundaryUp.mk contextSource' selfQuery' rejection' stratification'
        provenance' transport' route' package' name' =
      RussellSelfMembershipBoundaryUp.mk contextSource selfQuery rejection stratification provenance
        transport route package name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hContextSource
  cases hSelfQuery
  cases hRejection
  cases hStratification
  cases hProvenance
  cases hTransport
  cases hRoute
  cases hPackage
  cases hName
  rfl

def russellSelfMembershipBoundaryToEventFlow : RussellSelfMembershipBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RussellSelfMembershipBoundaryUp.mk contextSource selfQuery rejection stratification provenance
      transport route package name =>
      [[BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist contextSource,
        [BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist selfQuery,
        [BMark.b1, BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist rejection,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist stratification,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        russellSelfMembershipBoundaryEncodeBHist name]

def russellSelfMembershipBoundaryFromEventFlow :
    EventFlow → Option RussellSelfMembershipBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | contextSource :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | selfQuery :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | rejection :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stratification :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
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
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | package :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RussellSelfMembershipBoundaryUp.mk
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    contextSource)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    selfQuery)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    rejection)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    stratification)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    provenance)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    transport)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    route)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    package)
                                                                                  (russellSelfMembershipBoundaryDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem russellSelfMembershipBoundary_round_trip :
    ∀ x : RussellSelfMembershipBoundaryUp,
      russellSelfMembershipBoundaryFromEventFlow
        (russellSelfMembershipBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk contextSource selfQuery rejection stratification provenance transport route package name =>
      change
        some
            (RussellSelfMembershipBoundaryUp.mk
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist contextSource))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist selfQuery))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist rejection))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist stratification))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist provenance))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist transport))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist route))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist package))
              (russellSelfMembershipBoundaryDecodeBHist
                (russellSelfMembershipBoundaryEncodeBHist name))) =
          some
            (RussellSelfMembershipBoundaryUp.mk contextSource selfQuery rejection stratification
              provenance transport route package name)
      exact
        congrArg some
          (russellSelfMembershipBoundary_mk_congr
            (russellSelfMembershipBoundaryDecode_encode_bhist contextSource)
            (russellSelfMembershipBoundaryDecode_encode_bhist selfQuery)
            (russellSelfMembershipBoundaryDecode_encode_bhist rejection)
            (russellSelfMembershipBoundaryDecode_encode_bhist stratification)
            (russellSelfMembershipBoundaryDecode_encode_bhist provenance)
            (russellSelfMembershipBoundaryDecode_encode_bhist transport)
            (russellSelfMembershipBoundaryDecode_encode_bhist route)
            (russellSelfMembershipBoundaryDecode_encode_bhist package)
            (russellSelfMembershipBoundaryDecode_encode_bhist name))

private theorem russellSelfMembershipBoundaryToEventFlow_injective
    {x y : RussellSelfMembershipBoundaryUp} :
    russellSelfMembershipBoundaryToEventFlow x =
        russellSelfMembershipBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      russellSelfMembershipBoundaryFromEventFlow
          (russellSelfMembershipBoundaryToEventFlow x) =
        russellSelfMembershipBoundaryFromEventFlow
          (russellSelfMembershipBoundaryToEventFlow y) :=
    congrArg russellSelfMembershipBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (russellSelfMembershipBoundary_round_trip x).symm
      (Eq.trans hread (russellSelfMembershipBoundary_round_trip y)))

instance russellSelfMembershipBoundaryBHistCarrier :
    BHistCarrier RussellSelfMembershipBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := russellSelfMembershipBoundaryToEventFlow
  fromEventFlow := russellSelfMembershipBoundaryFromEventFlow

instance russellSelfMembershipBoundaryChapterTasteGate :
    ChapterTasteGate RussellSelfMembershipBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      russellSelfMembershipBoundaryFromEventFlow
        (russellSelfMembershipBoundaryToEventFlow x) = some x
    exact russellSelfMembershipBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (russellSelfMembershipBoundaryToEventFlow_injective heq)

theorem RussellSelfMembershipBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        russellSelfMembershipBoundaryDecodeBHist
          (russellSelfMembershipBoundaryEncodeBHist h) = h) ∧
      (∀ x : RussellSelfMembershipBoundaryUp,
        russellSelfMembershipBoundaryFromEventFlow
          (russellSelfMembershipBoundaryToEventFlow x) = some x) ∧
        (∀ x y : RussellSelfMembershipBoundaryUp,
          russellSelfMembershipBoundaryToEventFlow x =
              russellSelfMembershipBoundaryToEventFlow y →
            x = y) ∧
          russellSelfMembershipBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact russellSelfMembershipBoundaryDecode_encode_bhist
  · constructor
    · exact russellSelfMembershipBoundary_round_trip
    · constructor
      · intro x y heq
        exact russellSelfMembershipBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.RussellSelfMembershipBoundaryUp
