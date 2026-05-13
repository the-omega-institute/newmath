import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICClosurePreservationAuditUp : Type where
  | mk :
      (auditMap auditSeal shiftClosed varSubstClosed substClosed betaClosed betaStarClosed
        subjectReductionFrontier transport route provenance name : BHist) →
      MetaCICClosurePreservationAuditUp
  deriving DecidableEq

private def metaCICClosurePreservationAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICClosurePreservationAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICClosurePreservationAuditEncodeBHist h

private def metaCICClosurePreservationAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICClosurePreservationAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICClosurePreservationAuditDecodeBHist tail)

private theorem metaCICClosurePreservationAuditDecode_encode_bhist :
    ∀ h : BHist,
      metaCICClosurePreservationAuditDecodeBHist
          (metaCICClosurePreservationAuditEncodeBHist h) =
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

private theorem metaCICClosurePreservationAudit_mk_congr
    {auditMap auditMap' auditSeal auditSeal' shiftClosed shiftClosed'
      varSubstClosed varSubstClosed' substClosed substClosed' betaClosed betaClosed'
      betaStarClosed betaStarClosed' subjectReductionFrontier subjectReductionFrontier'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hAuditMap : auditMap' = auditMap)
    (hAuditSeal : auditSeal' = auditSeal)
    (hShiftClosed : shiftClosed' = shiftClosed)
    (hVarSubstClosed : varSubstClosed' = varSubstClosed)
    (hSubstClosed : substClosed' = substClosed)
    (hBetaClosed : betaClosed' = betaClosed)
    (hBetaStarClosed : betaStarClosed' = betaStarClosed)
    (hSubjectReductionFrontier :
      subjectReductionFrontier' = subjectReductionFrontier)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    MetaCICClosurePreservationAuditUp.mk auditMap' auditSeal' shiftClosed'
        varSubstClosed' substClosed' betaClosed' betaStarClosed'
        subjectReductionFrontier' transport' route' provenance' name' =
      MetaCICClosurePreservationAuditUp.mk auditMap auditSeal shiftClosed varSubstClosed
        substClosed betaClosed betaStarClosed subjectReductionFrontier transport route
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAuditMap
  cases hAuditSeal
  cases hShiftClosed
  cases hVarSubstClosed
  cases hSubstClosed
  cases hBetaClosed
  cases hBetaStarClosed
  cases hSubjectReductionFrontier
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private def metaCICClosurePreservationAuditToEventFlow :
    MetaCICClosurePreservationAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICClosurePreservationAuditUp.mk auditMap auditSeal shiftClosed varSubstClosed
      substClosed betaClosed betaStarClosed subjectReductionFrontier transport route
      provenance name =>
      [[BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist auditMap,
        [BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist auditSeal,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist shiftClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist varSubstClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist substClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist betaClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist betaStarClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist subjectReductionFrontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICClosurePreservationAuditEncodeBHist name]

private def metaCICClosurePreservationAuditFromEventFlow :
    EventFlow → Option MetaCICClosurePreservationAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | auditMap :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | auditSeal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | shiftClosed :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | varSubstClosed :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | substClosed :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | betaClosed :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | betaStarClosed :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | subjectReductionFrontier :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | route :: rest19 =>
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
                                                                                                        (MetaCICClosurePreservationAuditUp.mk
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist auditMap)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist auditSeal)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist shiftClosed)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist varSubstClosed)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist substClosed)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist betaClosed)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist betaStarClosed)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist subjectReductionFrontier)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist transport)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist route)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist provenance)
                                                                                                          (metaCICClosurePreservationAuditDecodeBHist name))
                                                                                                  | _ :: _ => none

private theorem metaCICClosurePreservationAudit_round_trip :
    ∀ x : MetaCICClosurePreservationAuditUp,
      metaCICClosurePreservationAuditFromEventFlow
          (metaCICClosurePreservationAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk auditMap auditSeal shiftClosed varSubstClosed substClosed betaClosed
      betaStarClosed subjectReductionFrontier transport route provenance name =>
      change
        some
          (MetaCICClosurePreservationAuditUp.mk
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist auditMap))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist auditSeal))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist shiftClosed))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist varSubstClosed))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist substClosed))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist betaClosed))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist betaStarClosed))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist subjectReductionFrontier))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist transport))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist route))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist provenance))
            (metaCICClosurePreservationAuditDecodeBHist
              (metaCICClosurePreservationAuditEncodeBHist name))) =
          some
            (MetaCICClosurePreservationAuditUp.mk auditMap auditSeal shiftClosed
              varSubstClosed substClosed betaClosed betaStarClosed subjectReductionFrontier
              transport route provenance name)
      exact
        congrArg some
          (metaCICClosurePreservationAudit_mk_congr
            (metaCICClosurePreservationAuditDecode_encode_bhist auditMap)
            (metaCICClosurePreservationAuditDecode_encode_bhist auditSeal)
            (metaCICClosurePreservationAuditDecode_encode_bhist shiftClosed)
            (metaCICClosurePreservationAuditDecode_encode_bhist varSubstClosed)
            (metaCICClosurePreservationAuditDecode_encode_bhist substClosed)
            (metaCICClosurePreservationAuditDecode_encode_bhist betaClosed)
            (metaCICClosurePreservationAuditDecode_encode_bhist betaStarClosed)
            (metaCICClosurePreservationAuditDecode_encode_bhist subjectReductionFrontier)
            (metaCICClosurePreservationAuditDecode_encode_bhist transport)
            (metaCICClosurePreservationAuditDecode_encode_bhist route)
            (metaCICClosurePreservationAuditDecode_encode_bhist provenance)
            (metaCICClosurePreservationAuditDecode_encode_bhist name))

private theorem metaCICClosurePreservationAuditToEventFlow_injective
    {x y : MetaCICClosurePreservationAuditUp} :
    metaCICClosurePreservationAuditToEventFlow x =
        metaCICClosurePreservationAuditToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICClosurePreservationAuditFromEventFlow
          (metaCICClosurePreservationAuditToEventFlow x) =
        metaCICClosurePreservationAuditFromEventFlow
          (metaCICClosurePreservationAuditToEventFlow y) :=
    congrArg metaCICClosurePreservationAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICClosurePreservationAudit_round_trip x).symm
      (Eq.trans hread (metaCICClosurePreservationAudit_round_trip y)))

instance metaCICClosurePreservationAuditBHistCarrier :
    BHistCarrier MetaCICClosurePreservationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICClosurePreservationAuditToEventFlow
  fromEventFlow := metaCICClosurePreservationAuditFromEventFlow

instance metaCICClosurePreservationAuditChapterTasteGate :
    ChapterTasteGate MetaCICClosurePreservationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICClosurePreservationAuditFromEventFlow
          (metaCICClosurePreservationAuditToEventFlow x) =
        some x
    exact metaCICClosurePreservationAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICClosurePreservationAuditToEventFlow_injective heq)

theorem MetaCICClosurePreservationAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICClosurePreservationAuditDecodeBHist
          (metaCICClosurePreservationAuditEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICClosurePreservationAuditUp,
        metaCICClosurePreservationAuditFromEventFlow
            (metaCICClosurePreservationAuditToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICClosurePreservationAuditUp,
          metaCICClosurePreservationAuditToEventFlow x =
              metaCICClosurePreservationAuditToEventFlow y →
            x = y) ∧
          metaCICClosurePreservationAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICClosurePreservationAuditDecode_encode_bhist
  · constructor
    · exact metaCICClosurePreservationAudit_round_trip
    · constructor
      · intro x y heq
        exact metaCICClosurePreservationAuditToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICClosurePreservationAuditUp
