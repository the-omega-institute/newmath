import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CounterfactualOutcomeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CounterfactualOutcomeUp : Type where
  | mk :
      (unitRow intervention factual counterfactual modified consistency transport distribution
        expectation replay provenance name : BHist) →
        CounterfactualOutcomeUp
  deriving DecidableEq

private def counterfactualOutcomeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: counterfactualOutcomeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: counterfactualOutcomeEncodeBHist h

private def counterfactualOutcomeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (counterfactualOutcomeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (counterfactualOutcomeDecodeBHist tail)

private theorem counterfactualOutcomeDecodeEncodeBHist :
    ∀ h : BHist, counterfactualOutcomeDecodeBHist
      (counterfactualOutcomeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem counterfactualOutcome_mk_congr
    {unitRow unitRow' intervention intervention' factual factual' counterfactual
      counterfactual' modified modified' consistency consistency' transport transport'
      distribution distribution' expectation expectation' replay replay' provenance provenance'
      name name' : BHist}
    (hUnitRow : unitRow' = unitRow)
    (hIntervention : intervention' = intervention)
    (hFactual : factual' = factual)
    (hCounterfactual : counterfactual' = counterfactual)
    (hModified : modified' = modified)
    (hConsistency : consistency' = consistency)
    (hTransport : transport' = transport)
    (hDistribution : distribution' = distribution)
    (hExpectation : expectation' = expectation)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CounterfactualOutcomeUp.mk unitRow' intervention' factual' counterfactual' modified'
        consistency' transport' distribution' expectation' replay' provenance' name' =
      CounterfactualOutcomeUp.mk unitRow intervention factual counterfactual modified
        consistency transport distribution expectation replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hUnitRow
  cases hIntervention
  cases hFactual
  cases hCounterfactual
  cases hModified
  cases hConsistency
  cases hTransport
  cases hDistribution
  cases hExpectation
  cases hReplay
  cases hProvenance
  cases hName
  rfl

private def counterfactualOutcomeToEventFlow : CounterfactualOutcomeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CounterfactualOutcomeUp.mk unitRow intervention factual counterfactual modified
      consistency transport distribution expectation replay provenance name =>
      [[BMark.b0],
        counterfactualOutcomeEncodeBHist unitRow,
        [BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist intervention,
        [BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist factual,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist counterfactual,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist modified,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist consistency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        counterfactualOutcomeEncodeBHist distribution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist expectation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        counterfactualOutcomeEncodeBHist name]

private def counterfactualOutcomeFromEventFlow :
    EventFlow → Option CounterfactualOutcomeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | unitRow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | intervention :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | factual :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | counterfactual :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | modified :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | consistency :: rest11 =>
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
                                                              | distribution :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | expectation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | replay :: rest19 =>
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
                                                                                                        (CounterfactualOutcomeUp.mk
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            unitRow)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            intervention)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            factual)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            counterfactual)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            modified)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            consistency)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            transport)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            distribution)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            expectation)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            replay)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            provenance)
                                                                                                          (counterfactualOutcomeDecodeBHist
                                                                                                            name))
                                                                                                  | _ :: _ => none

private theorem counterfactualOutcomeRoundTrip :
    ∀ x : CounterfactualOutcomeUp,
      counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk unitRow intervention factual counterfactual modified consistency transport distribution
      expectation replay provenance name =>
      change
        some
          (CounterfactualOutcomeUp.mk
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist unitRow))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist intervention))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist factual))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist counterfactual))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist modified))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist consistency))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist transport))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist distribution))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist expectation))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist replay))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist provenance))
            (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist name))) =
          some
            (CounterfactualOutcomeUp.mk unitRow intervention factual counterfactual modified
              consistency transport distribution expectation replay provenance name)
      exact
        congrArg some
          (counterfactualOutcome_mk_congr
            (counterfactualOutcomeDecodeEncodeBHist unitRow)
            (counterfactualOutcomeDecodeEncodeBHist intervention)
            (counterfactualOutcomeDecodeEncodeBHist factual)
            (counterfactualOutcomeDecodeEncodeBHist counterfactual)
            (counterfactualOutcomeDecodeEncodeBHist modified)
            (counterfactualOutcomeDecodeEncodeBHist consistency)
            (counterfactualOutcomeDecodeEncodeBHist transport)
            (counterfactualOutcomeDecodeEncodeBHist distribution)
            (counterfactualOutcomeDecodeEncodeBHist expectation)
            (counterfactualOutcomeDecodeEncodeBHist replay)
            (counterfactualOutcomeDecodeEncodeBHist provenance)
            (counterfactualOutcomeDecodeEncodeBHist name))

private theorem counterfactualOutcomeToEventFlow_injective
    {x y : CounterfactualOutcomeUp} :
    counterfactualOutcomeToEventFlow x = counterfactualOutcomeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) =
        counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow y) :=
    congrArg counterfactualOutcomeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (counterfactualOutcomeRoundTrip x).symm
      (Eq.trans hread (counterfactualOutcomeRoundTrip y)))

private def counterfactualOutcomeFields : CounterfactualOutcomeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CounterfactualOutcomeUp.mk unitRow intervention factual counterfactual modified
      consistency transport distribution expectation replay provenance name =>
      [unitRow, intervention, factual, counterfactual, modified, consistency, transport,
        distribution, expectation, replay, provenance, name]

private theorem counterfactualOutcome_field_faithful :
    ∀ x y : CounterfactualOutcomeUp,
      counterfactualOutcomeFields x = counterfactualOutcomeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk unitRow intervention factual counterfactual modified consistency transport distribution
      expectation replay provenance name =>
      cases y with
      | mk unitRow' intervention' factual' counterfactual' modified' consistency' transport'
          distribution' expectation' replay' provenance' name' =>
          cases hfields
          rfl

instance counterfactualOutcomeBHistCarrier : BHistCarrier CounterfactualOutcomeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := counterfactualOutcomeToEventFlow
  fromEventFlow := counterfactualOutcomeFromEventFlow

instance counterfactualOutcomeChapterTasteGate :
    ChapterTasteGate CounterfactualOutcomeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) = some x
    exact counterfactualOutcomeRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (counterfactualOutcomeToEventFlow_injective heq)

instance counterfactualOutcomeFieldFaithful : FieldFaithful CounterfactualOutcomeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := counterfactualOutcomeFields
  field_faithful := counterfactualOutcome_field_faithful

instance counterfactualOutcomeNontrivial : Nontrivial CounterfactualOutcomeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CounterfactualOutcomeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CounterfactualOutcomeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CounterfactualOutcomeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  counterfactualOutcomeChapterTasteGate

theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, counterfactualOutcomeDecodeBHist
      (counterfactualOutcomeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact counterfactualOutcomeDecodeEncodeBHist

theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CounterfactualOutcomeUp,
      counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact counterfactualOutcomeRoundTrip

theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_injective :
    ∀ x y : CounterfactualOutcomeUp,
      counterfactualOutcomeToEventFlow x = counterfactualOutcomeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  exact fun _x _y heq => counterfactualOutcomeToEventFlow_injective heq

theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_empty :
    counterfactualOutcomeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

theorem CounterfactualOutcomeTasteGate_single_carrier_alignment :
    (∀ h : BHist, counterfactualOutcomeDecodeBHist
        (counterfactualOutcomeEncodeBHist h) = h) ∧
      (∀ x : CounterfactualOutcomeUp,
        counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) = some x) ∧
        (∀ x y : CounterfactualOutcomeUp,
          counterfactualOutcomeToEventFlow x = counterfactualOutcomeToEventFlow y → x = y) ∧
          counterfactualOutcomeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro CounterfactualOutcomeTasteGate_single_carrier_alignment_decode
      (And.intro CounterfactualOutcomeTasteGate_single_carrier_alignment_round_trip
        (And.intro CounterfactualOutcomeTasteGate_single_carrier_alignment_injective
          CounterfactualOutcomeTasteGate_single_carrier_alignment_empty))

end BEDC.Derived.CounterfactualOutcomeUp
