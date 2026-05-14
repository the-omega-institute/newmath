import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICClosurePreservationUp : Type where
  | mk :
      (shiftClosed varSubstClosed substClosed betaClosed betaStarClosed auditRow
        closedSeal generatorClassifier subjectReductionConsumer transport route
        provenance name : BHist) →
      MetaCICClosurePreservationUp
  deriving DecidableEq

private def metaCICClosurePreservationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICClosurePreservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICClosurePreservationEncodeBHist h

private def metaCICClosurePreservationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICClosurePreservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICClosurePreservationDecodeBHist tail)

private theorem metaCICClosurePreservationDecode_encode_bhist :
    ∀ h : BHist,
      metaCICClosurePreservationDecodeBHist
          (metaCICClosurePreservationEncodeBHist h) =
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

private def metaCICClosurePreservationToEventFlow :
    MetaCICClosurePreservationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICClosurePreservationUp.mk shiftClosed varSubstClosed substClosed
      betaClosed betaStarClosed auditRow closedSeal generatorClassifier
      subjectReductionConsumer transport route provenance name =>
      [[BMark.b0],
        metaCICClosurePreservationEncodeBHist shiftClosed,
        [BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist varSubstClosed,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist substClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist betaClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist betaStarClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist auditRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist closedSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICClosurePreservationEncodeBHist generatorClassifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist subjectReductionConsumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationEncodeBHist name]

private def metaCICClosurePreservationFromEventFlow :
    EventFlow → Option MetaCICClosurePreservationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | shiftClosed :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | varSubstClosed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | substClosed :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | betaClosed :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | betaStarClosed :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | auditRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | closedSeal :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | generatorClassifier :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | subjectReductionConsumer :: rest17 =>
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
                                                                                      | route :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | provenance :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | name :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (MetaCICClosurePreservationUp.mk
                                                                                                                  (metaCICClosurePreservationDecodeBHist shiftClosed)
                                                                                                                  (metaCICClosurePreservationDecodeBHist varSubstClosed)
                                                                                                                  (metaCICClosurePreservationDecodeBHist substClosed)
                                                                                                                  (metaCICClosurePreservationDecodeBHist betaClosed)
                                                                                                                  (metaCICClosurePreservationDecodeBHist betaStarClosed)
                                                                                                                  (metaCICClosurePreservationDecodeBHist auditRow)
                                                                                                                  (metaCICClosurePreservationDecodeBHist closedSeal)
                                                                                                                  (metaCICClosurePreservationDecodeBHist generatorClassifier)
                                                                                                                  (metaCICClosurePreservationDecodeBHist subjectReductionConsumer)
                                                                                                                  (metaCICClosurePreservationDecodeBHist transport)
                                                                                                                  (metaCICClosurePreservationDecodeBHist route)
                                                                                                                  (metaCICClosurePreservationDecodeBHist provenance)
                                                                                                                  (metaCICClosurePreservationDecodeBHist name))
                                                                                                          | _ :: _ => none

private theorem metaCICClosurePreservation_round_trip :
    ∀ x : MetaCICClosurePreservationUp,
      metaCICClosurePreservationFromEventFlow
          (metaCICClosurePreservationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk shiftClosed varSubstClosed substClosed betaClosed betaStarClosed auditRow
      closedSeal generatorClassifier subjectReductionConsumer transport route provenance name =>
      change
        some
          (MetaCICClosurePreservationUp.mk
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist shiftClosed))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist varSubstClosed))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist substClosed))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist betaClosed))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist betaStarClosed))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist auditRow))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist closedSeal))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist generatorClassifier))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist subjectReductionConsumer))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist transport))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist route))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist provenance))
            (metaCICClosurePreservationDecodeBHist
              (metaCICClosurePreservationEncodeBHist name))) =
          some
            (MetaCICClosurePreservationUp.mk shiftClosed varSubstClosed substClosed
              betaClosed betaStarClosed auditRow closedSeal generatorClassifier
              subjectReductionConsumer transport route provenance name)
      rw [metaCICClosurePreservationDecode_encode_bhist shiftClosed,
        metaCICClosurePreservationDecode_encode_bhist varSubstClosed,
        metaCICClosurePreservationDecode_encode_bhist substClosed,
        metaCICClosurePreservationDecode_encode_bhist betaClosed,
        metaCICClosurePreservationDecode_encode_bhist betaStarClosed,
        metaCICClosurePreservationDecode_encode_bhist auditRow,
        metaCICClosurePreservationDecode_encode_bhist closedSeal,
        metaCICClosurePreservationDecode_encode_bhist generatorClassifier,
        metaCICClosurePreservationDecode_encode_bhist subjectReductionConsumer,
        metaCICClosurePreservationDecode_encode_bhist transport,
        metaCICClosurePreservationDecode_encode_bhist route,
        metaCICClosurePreservationDecode_encode_bhist provenance,
        metaCICClosurePreservationDecode_encode_bhist name]

private theorem metaCICClosurePreservationToEventFlow_injective
    {x y : MetaCICClosurePreservationUp} :
    metaCICClosurePreservationToEventFlow x =
        metaCICClosurePreservationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICClosurePreservationFromEventFlow
          (metaCICClosurePreservationToEventFlow x) =
        metaCICClosurePreservationFromEventFlow
          (metaCICClosurePreservationToEventFlow y) :=
    congrArg metaCICClosurePreservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICClosurePreservation_round_trip x).symm
      (Eq.trans hread (metaCICClosurePreservation_round_trip y)))

instance metaCICClosurePreservationBHistCarrier :
    BHistCarrier MetaCICClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICClosurePreservationToEventFlow
  fromEventFlow := metaCICClosurePreservationFromEventFlow

instance metaCICClosurePreservationChapterTasteGate :
    ChapterTasteGate MetaCICClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICClosurePreservationFromEventFlow
          (metaCICClosurePreservationToEventFlow x) =
        some x
    exact metaCICClosurePreservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICClosurePreservationToEventFlow_injective heq)

instance metaCICClosurePreservationFieldFaithful :
    FieldFaithful MetaCICClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICClosurePreservationUp.mk shiftClosed varSubstClosed substClosed
        betaClosed betaStarClosed auditRow closedSeal generatorClassifier
        subjectReductionConsumer transport route provenance name =>
        [shiftClosed, varSubstClosed, substClosed, betaClosed, betaStarClosed,
          auditRow, closedSeal, generatorClassifier, subjectReductionConsumer,
          transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk shiftClosed1 varSubstClosed1 substClosed1 betaClosed1 betaStarClosed1
        auditRow1 closedSeal1 generatorClassifier1 subjectReductionConsumer1
        transport1 route1 provenance1 name1 =>
        cases y with
        | mk shiftClosed2 varSubstClosed2 substClosed2 betaClosed2 betaStarClosed2
            auditRow2 closedSeal2 generatorClassifier2 subjectReductionConsumer2
            transport2 route2 provenance2 name2 =>
            injection h with hShiftClosed tail1
            cases hShiftClosed
            injection tail1 with hVarSubstClosed tail2
            cases hVarSubstClosed
            injection tail2 with hSubstClosed tail3
            cases hSubstClosed
            injection tail3 with hBetaClosed tail4
            cases hBetaClosed
            injection tail4 with hBetaStarClosed tail5
            cases hBetaStarClosed
            injection tail5 with hAuditRow tail6
            cases hAuditRow
            injection tail6 with hClosedSeal tail7
            cases hClosedSeal
            injection tail7 with hGeneratorClassifier tail8
            cases hGeneratorClassifier
            injection tail8 with hSubjectReductionConsumer tail9
            cases hSubjectReductionConsumer
            injection tail9 with hTransport tail10
            cases hTransport
            injection tail10 with hRoute tail11
            cases hRoute
            injection tail11 with hProvenance tail12
            cases hProvenance
            injection tail12 with hName _
            cases hName
            rfl

theorem MetaCICClosurePreservationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICClosurePreservationDecodeBHist
          (metaCICClosurePreservationEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICClosurePreservationUp,
        metaCICClosurePreservationFromEventFlow
            (metaCICClosurePreservationToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICClosurePreservationUp,
          metaCICClosurePreservationToEventFlow x =
              metaCICClosurePreservationToEventFlow y →
            x = y) ∧
          metaCICClosurePreservationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICClosurePreservationDecode_encode_bhist
  · constructor
    · exact metaCICClosurePreservation_round_trip
    · constructor
      · intro x y heq
        exact metaCICClosurePreservationToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICClosurePreservationUp
