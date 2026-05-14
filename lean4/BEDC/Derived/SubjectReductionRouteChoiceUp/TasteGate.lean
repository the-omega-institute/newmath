import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionRouteChoiceUp : Type where
  | mk :
      (bundle setup setupToBundle bundleConsumption setupConsumption obstruction
        transport route provenance name : BHist) →
      SubjectReductionRouteChoiceUp
  deriving DecidableEq

private def subjectReductionRouteChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionRouteChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionRouteChoiceEncodeBHist h

private def subjectReductionRouteChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionRouteChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionRouteChoiceDecodeBHist tail)

private theorem subjectReductionRouteChoiceDecode_encode_bhist :
    ∀ h : BHist,
      subjectReductionRouteChoiceDecodeBHist
          (subjectReductionRouteChoiceEncodeBHist h) =
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

private def subjectReductionRouteChoiceToEventFlow :
    SubjectReductionRouteChoiceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionRouteChoiceUp.mk bundle setup setupToBundle bundleConsumption
      setupConsumption obstruction transport route provenance name =>
      [[BMark.b0],
        subjectReductionRouteChoiceEncodeBHist bundle,
        [BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist setup,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist setupToBundle,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist bundleConsumption,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist setupConsumption,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionRouteChoiceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subjectReductionRouteChoiceEncodeBHist name]

private def subjectReductionRouteChoiceFromEventFlow :
    EventFlow → Option SubjectReductionRouteChoiceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | bundle :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | setup :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | setupToBundle :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | bundleConsumption :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | setupConsumption :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | obstruction :: rest11 =>
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
                                                                                        (SubjectReductionRouteChoiceUp.mk
                                                                                          (subjectReductionRouteChoiceDecodeBHist bundle)
                                                                                          (subjectReductionRouteChoiceDecodeBHist setup)
                                                                                          (subjectReductionRouteChoiceDecodeBHist setupToBundle)
                                                                                          (subjectReductionRouteChoiceDecodeBHist bundleConsumption)
                                                                                          (subjectReductionRouteChoiceDecodeBHist setupConsumption)
                                                                                          (subjectReductionRouteChoiceDecodeBHist obstruction)
                                                                                          (subjectReductionRouteChoiceDecodeBHist transport)
                                                                                          (subjectReductionRouteChoiceDecodeBHist route)
                                                                                          (subjectReductionRouteChoiceDecodeBHist provenance)
                                                                                          (subjectReductionRouteChoiceDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem subjectReductionRouteChoice_round_trip :
    ∀ x : SubjectReductionRouteChoiceUp,
      subjectReductionRouteChoiceFromEventFlow
          (subjectReductionRouteChoiceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bundle setup setupToBundle bundleConsumption setupConsumption obstruction
      transport route provenance name =>
      change
        some
          (SubjectReductionRouteChoiceUp.mk
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist bundle))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist setup))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist setupToBundle))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist bundleConsumption))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist setupConsumption))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist obstruction))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist transport))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist route))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist provenance))
            (subjectReductionRouteChoiceDecodeBHist
              (subjectReductionRouteChoiceEncodeBHist name))) =
          some
            (SubjectReductionRouteChoiceUp.mk bundle setup setupToBundle
              bundleConsumption setupConsumption obstruction transport route provenance name)
      rw [subjectReductionRouteChoiceDecode_encode_bhist bundle,
        subjectReductionRouteChoiceDecode_encode_bhist setup,
        subjectReductionRouteChoiceDecode_encode_bhist setupToBundle,
        subjectReductionRouteChoiceDecode_encode_bhist bundleConsumption,
        subjectReductionRouteChoiceDecode_encode_bhist setupConsumption,
        subjectReductionRouteChoiceDecode_encode_bhist obstruction,
        subjectReductionRouteChoiceDecode_encode_bhist transport,
        subjectReductionRouteChoiceDecode_encode_bhist route,
        subjectReductionRouteChoiceDecode_encode_bhist provenance,
        subjectReductionRouteChoiceDecode_encode_bhist name]

private theorem subjectReductionRouteChoiceToEventFlow_injective
    {x y : SubjectReductionRouteChoiceUp} :
    subjectReductionRouteChoiceToEventFlow x =
        subjectReductionRouteChoiceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionRouteChoiceFromEventFlow
          (subjectReductionRouteChoiceToEventFlow x) =
        subjectReductionRouteChoiceFromEventFlow
          (subjectReductionRouteChoiceToEventFlow y) :=
    congrArg subjectReductionRouteChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionRouteChoice_round_trip x).symm
      (Eq.trans hread (subjectReductionRouteChoice_round_trip y)))

instance subjectReductionRouteChoiceBHistCarrier :
    BHistCarrier SubjectReductionRouteChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionRouteChoiceToEventFlow
  fromEventFlow := subjectReductionRouteChoiceFromEventFlow

instance subjectReductionRouteChoiceChapterTasteGate :
    ChapterTasteGate SubjectReductionRouteChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionRouteChoiceFromEventFlow
          (subjectReductionRouteChoiceToEventFlow x) =
        some x
    exact subjectReductionRouteChoice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionRouteChoiceToEventFlow_injective heq)

instance subjectReductionRouteChoiceFieldFaithful :
    FieldFaithful SubjectReductionRouteChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubjectReductionRouteChoiceUp.mk bundle setup setupToBundle bundleConsumption
        setupConsumption obstruction transport route provenance name =>
        [bundle, setup, setupToBundle, bundleConsumption, setupConsumption, obstruction,
          transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk bundle1 setup1 setupToBundle1 bundleConsumption1 setupConsumption1 obstruction1
        transport1 route1 provenance1 name1 =>
        cases y with
        | mk bundle2 setup2 setupToBundle2 bundleConsumption2 setupConsumption2 obstruction2
            transport2 route2 provenance2 name2 =>
            injection h with hBundle t1
            injection t1 with hSetup t2
            injection t2 with hSetupToBundle t3
            injection t3 with hBundleConsumption t4
            injection t4 with hSetupConsumption t5
            injection t5 with hObstruction t6
            injection t6 with hTransport t7
            injection t7 with hRoute t8
            injection t8 with hProvenance t9
            injection t9 with hName _
            cases hBundle
            cases hSetup
            cases hSetupToBundle
            cases hBundleConsumption
            cases hSetupConsumption
            cases hObstruction
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem SubjectReductionRouteChoiceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      subjectReductionRouteChoiceDecodeBHist
          (subjectReductionRouteChoiceEncodeBHist h) =
        h) ∧
      (∀ x : SubjectReductionRouteChoiceUp,
        subjectReductionRouteChoiceFromEventFlow
            (subjectReductionRouteChoiceToEventFlow x) =
          some x) ∧
        (∀ x y : SubjectReductionRouteChoiceUp,
          subjectReductionRouteChoiceToEventFlow x =
              subjectReductionRouteChoiceToEventFlow y →
            x = y) ∧
          subjectReductionRouteChoiceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subjectReductionRouteChoiceDecode_encode_bhist
  · constructor
    · exact subjectReductionRouteChoice_round_trip
    · constructor
      · intro x y heq
        exact subjectReductionRouteChoiceToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubjectReductionRouteChoiceUp
