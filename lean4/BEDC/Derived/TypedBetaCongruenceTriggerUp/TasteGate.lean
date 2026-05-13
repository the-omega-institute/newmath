import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypedBetaCongruenceTriggerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypedBetaCongruenceTriggerUp : Type where
  | mk :
      (constructorTag betaStep sourceTerm judgementBoundary auditBoundary dischargeRow
        transport route provenance name : BHist) →
      TypedBetaCongruenceTriggerUp
  deriving DecidableEq

private def typedBetaCongruenceTriggerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typedBetaCongruenceTriggerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typedBetaCongruenceTriggerEncodeBHist h

private def typedBetaCongruenceTriggerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typedBetaCongruenceTriggerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typedBetaCongruenceTriggerDecodeBHist tail)

private theorem typedBetaCongruenceTriggerDecode_encode_bhist :
    ∀ h : BHist,
      typedBetaCongruenceTriggerDecodeBHist
          (typedBetaCongruenceTriggerEncodeBHist h) =
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

private def typedBetaCongruenceTriggerToEventFlow :
    TypedBetaCongruenceTriggerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypedBetaCongruenceTriggerUp.mk constructorTag betaStep sourceTerm
      judgementBoundary auditBoundary dischargeRow transport route provenance name =>
      [[BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist constructorTag,
        [BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist betaStep,
        [BMark.b1, BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist sourceTerm,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist judgementBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist auditBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist dischargeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        typedBetaCongruenceTriggerEncodeBHist name]

private def typedBetaCongruenceTriggerFromEventFlow :
    EventFlow → Option TypedBetaCongruenceTriggerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | constructorTag :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | betaStep :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sourceTerm :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | judgementBoundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | auditBoundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | dischargeRow :: rest11 =>
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
                                                                                        (TypedBetaCongruenceTriggerUp.mk
                                                                                          (typedBetaCongruenceTriggerDecodeBHist constructorTag)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist betaStep)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist sourceTerm)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist judgementBoundary)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist auditBoundary)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist dischargeRow)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist transport)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist route)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist provenance)
                                                                                          (typedBetaCongruenceTriggerDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem typedBetaCongruenceTrigger_round_trip :
    ∀ x : TypedBetaCongruenceTriggerUp,
      typedBetaCongruenceTriggerFromEventFlow
          (typedBetaCongruenceTriggerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk constructorTag betaStep sourceTerm judgementBoundary auditBoundary dischargeRow
      transport route provenance name =>
      change
        some
          (TypedBetaCongruenceTriggerUp.mk
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist constructorTag))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist betaStep))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist sourceTerm))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist judgementBoundary))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist auditBoundary))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist dischargeRow))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist transport))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist route))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist provenance))
            (typedBetaCongruenceTriggerDecodeBHist
              (typedBetaCongruenceTriggerEncodeBHist name))) =
          some
            (TypedBetaCongruenceTriggerUp.mk constructorTag betaStep sourceTerm
              judgementBoundary auditBoundary dischargeRow transport route provenance name)
      rw [typedBetaCongruenceTriggerDecode_encode_bhist constructorTag,
        typedBetaCongruenceTriggerDecode_encode_bhist betaStep,
        typedBetaCongruenceTriggerDecode_encode_bhist sourceTerm,
        typedBetaCongruenceTriggerDecode_encode_bhist judgementBoundary,
        typedBetaCongruenceTriggerDecode_encode_bhist auditBoundary,
        typedBetaCongruenceTriggerDecode_encode_bhist dischargeRow,
        typedBetaCongruenceTriggerDecode_encode_bhist transport,
        typedBetaCongruenceTriggerDecode_encode_bhist route,
        typedBetaCongruenceTriggerDecode_encode_bhist provenance,
        typedBetaCongruenceTriggerDecode_encode_bhist name]

private theorem typedBetaCongruenceTriggerToEventFlow_injective
    {x y : TypedBetaCongruenceTriggerUp} :
    typedBetaCongruenceTriggerToEventFlow x =
        typedBetaCongruenceTriggerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typedBetaCongruenceTriggerFromEventFlow
          (typedBetaCongruenceTriggerToEventFlow x) =
        typedBetaCongruenceTriggerFromEventFlow
          (typedBetaCongruenceTriggerToEventFlow y) :=
    congrArg typedBetaCongruenceTriggerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typedBetaCongruenceTrigger_round_trip x).symm
      (Eq.trans hread (typedBetaCongruenceTrigger_round_trip y)))

instance typedBetaCongruenceTriggerBHistCarrier :
    BHistCarrier TypedBetaCongruenceTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typedBetaCongruenceTriggerToEventFlow
  fromEventFlow := typedBetaCongruenceTriggerFromEventFlow

instance typedBetaCongruenceTriggerChapterTasteGate :
    ChapterTasteGate TypedBetaCongruenceTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typedBetaCongruenceTriggerFromEventFlow
          (typedBetaCongruenceTriggerToEventFlow x) =
        some x
    exact typedBetaCongruenceTrigger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typedBetaCongruenceTriggerToEventFlow_injective heq)

instance typedBetaCongruenceTriggerFieldFaithful :
    FieldFaithful TypedBetaCongruenceTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TypedBetaCongruenceTriggerUp.mk constructorTag betaStep sourceTerm
        judgementBoundary auditBoundary dischargeRow transport route provenance name =>
        [constructorTag, betaStep, sourceTerm, judgementBoundary, auditBoundary,
          dischargeRow, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk constructorTag1 betaStep1 sourceTerm1 judgementBoundary1 auditBoundary1
        dischargeRow1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk constructorTag2 betaStep2 sourceTerm2 judgementBoundary2 auditBoundary2
            dischargeRow2 transport2 route2 provenance2 name2 =>
            injection h with hConstructorTag tail1
            cases hConstructorTag
            injection tail1 with hBetaStep tail2
            cases hBetaStep
            injection tail2 with hSourceTerm tail3
            cases hSourceTerm
            injection tail3 with hJudgementBoundary tail4
            cases hJudgementBoundary
            injection tail4 with hAuditBoundary tail5
            cases hAuditBoundary
            injection tail5 with hDischargeRow tail6
            cases hDischargeRow
            injection tail6 with hTransport tail7
            cases hTransport
            injection tail7 with hRoute tail8
            cases hRoute
            injection tail8 with hProvenance tail9
            cases hProvenance
            injection tail9 with hName _
            cases hName
            rfl

theorem TypedBetaCongruenceTriggerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      typedBetaCongruenceTriggerDecodeBHist
          (typedBetaCongruenceTriggerEncodeBHist h) =
        h) ∧
      (∀ x : TypedBetaCongruenceTriggerUp,
        typedBetaCongruenceTriggerFromEventFlow
            (typedBetaCongruenceTriggerToEventFlow x) =
          some x) ∧
        (∀ x y : TypedBetaCongruenceTriggerUp,
          typedBetaCongruenceTriggerToEventFlow x =
              typedBetaCongruenceTriggerToEventFlow y →
            x = y) ∧
          typedBetaCongruenceTriggerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact typedBetaCongruenceTriggerDecode_encode_bhist
  · constructor
    · exact typedBetaCongruenceTrigger_round_trip
    · constructor
      · intro x y heq
        exact typedBetaCongruenceTriggerToEventFlow_injective heq
      · rfl

end BEDC.Derived.TypedBetaCongruenceTriggerUp
