import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicConfluenceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicConfluenceAuditWitnessUp : Type where
  | mk :
      (parallelStep substitutionBoundary diamondHandoff confluenceHandoff obstruction
        transport route provenance nameCert : BHist) →
      MetacicConfluenceAuditWitnessUp
  deriving DecidableEq

private def metacicConfluenceAuditWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicConfluenceAuditWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicConfluenceAuditWitnessEncodeBHist h

private def metacicConfluenceAuditWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicConfluenceAuditWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicConfluenceAuditWitnessDecodeBHist tail)

private theorem metacicConfluenceAuditWitnessDecode_encode_bhist :
    ∀ h : BHist,
      metacicConfluenceAuditWitnessDecodeBHist
          (metacicConfluenceAuditWitnessEncodeBHist h) =
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

private theorem metacicConfluenceAuditWitness_mk_congr
    {parallelStep parallelStep' substitutionBoundary substitutionBoundary'
      diamondHandoff diamondHandoff' confluenceHandoff confluenceHandoff'
      obstruction obstruction' transport transport' route route' provenance provenance'
      nameCert nameCert' : BHist}
    (hParallelStep : parallelStep' = parallelStep)
    (hSubstitutionBoundary : substitutionBoundary' = substitutionBoundary)
    (hDiamondHandoff : diamondHandoff' = diamondHandoff)
    (hConfluenceHandoff : confluenceHandoff' = confluenceHandoff)
    (hObstruction : obstruction' = obstruction)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    MetacicConfluenceAuditWitnessUp.mk parallelStep' substitutionBoundary'
        diamondHandoff' confluenceHandoff' obstruction' transport' route' provenance'
        nameCert' =
      MetacicConfluenceAuditWitnessUp.mk parallelStep substitutionBoundary diamondHandoff
        confluenceHandoff obstruction transport route provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hParallelStep
  cases hSubstitutionBoundary
  cases hDiamondHandoff
  cases hConfluenceHandoff
  cases hObstruction
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

private def metacicConfluenceAuditWitnessToEventFlow :
    MetacicConfluenceAuditWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicConfluenceAuditWitnessUp.mk parallelStep substitutionBoundary diamondHandoff
      confluenceHandoff obstruction transport route provenance nameCert =>
      [[BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist parallelStep,
        [BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist substitutionBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist diamondHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist confluenceHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist nameCert]

private def metacicConfluenceAuditWitnessFromEventFlow :
    EventFlow → Option MetacicConfluenceAuditWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | parallelStep :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | substitutionBoundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diamondHandoff :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | confluenceHandoff :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | obstruction :: rest9 =>
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
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetacicConfluenceAuditWitnessUp.mk
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist parallelStep)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist substitutionBoundary)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist diamondHandoff)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist confluenceHandoff)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist obstruction)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist transport)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist route)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist provenance)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem metacicConfluenceAuditWitness_round_trip :
    ∀ x : MetacicConfluenceAuditWitnessUp,
      metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parallelStep substitutionBoundary diamondHandoff confluenceHandoff obstruction
      transport route provenance nameCert =>
      change
        some
          (MetacicConfluenceAuditWitnessUp.mk
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist parallelStep))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist substitutionBoundary))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist diamondHandoff))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist confluenceHandoff))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist obstruction))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist transport))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist route))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist provenance))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist nameCert))) =
          some
            (MetacicConfluenceAuditWitnessUp.mk parallelStep substitutionBoundary
              diamondHandoff confluenceHandoff obstruction transport route provenance nameCert)
      exact
        congrArg some
          (metacicConfluenceAuditWitness_mk_congr
            (metacicConfluenceAuditWitnessDecode_encode_bhist parallelStep)
            (metacicConfluenceAuditWitnessDecode_encode_bhist substitutionBoundary)
            (metacicConfluenceAuditWitnessDecode_encode_bhist diamondHandoff)
            (metacicConfluenceAuditWitnessDecode_encode_bhist confluenceHandoff)
            (metacicConfluenceAuditWitnessDecode_encode_bhist obstruction)
            (metacicConfluenceAuditWitnessDecode_encode_bhist transport)
            (metacicConfluenceAuditWitnessDecode_encode_bhist route)
            (metacicConfluenceAuditWitnessDecode_encode_bhist provenance)
            (metacicConfluenceAuditWitnessDecode_encode_bhist nameCert))

private theorem metacicConfluenceAuditWitnessToEventFlow_injective
    {x y : MetacicConfluenceAuditWitnessUp} :
    metacicConfluenceAuditWitnessToEventFlow x =
        metacicConfluenceAuditWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow x) =
        metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow y) :=
    congrArg metacicConfluenceAuditWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicConfluenceAuditWitness_round_trip x).symm
      (Eq.trans hread (metacicConfluenceAuditWitness_round_trip y)))

instance metacicConfluenceAuditWitnessBHistCarrier :
    BHistCarrier MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicConfluenceAuditWitnessToEventFlow
  fromEventFlow := metacicConfluenceAuditWitnessFromEventFlow

instance metacicConfluenceAuditWitnessChapterTasteGate :
    ChapterTasteGate MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow x) =
        some x
    exact metacicConfluenceAuditWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicConfluenceAuditWitnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow x) =
        some x
    exact metacicConfluenceAuditWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicConfluenceAuditWitnessToEventFlow_injective heq)

theorem MetacicConfluenceAuditWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicConfluenceAuditWitnessDecodeBHist
          (metacicConfluenceAuditWitnessEncodeBHist h) =
        h) ∧
      (∀ x : MetacicConfluenceAuditWitnessUp,
        metacicConfluenceAuditWitnessFromEventFlow
            (metacicConfluenceAuditWitnessToEventFlow x) =
          some x) ∧
        (∀ x y : MetacicConfluenceAuditWitnessUp,
          metacicConfluenceAuditWitnessToEventFlow x =
              metacicConfluenceAuditWitnessToEventFlow y →
            x = y) ∧
          metacicConfluenceAuditWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicConfluenceAuditWitnessDecode_encode_bhist
  · constructor
    · exact metacicConfluenceAuditWitness_round_trip
    · constructor
      · intro x y heq
        exact metacicConfluenceAuditWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetacicConfluenceAuditWitnessUp
