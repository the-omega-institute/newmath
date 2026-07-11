import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ParallelConfluenceAuditUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ParallelConfluenceAuditUp : Type where
  | mk :
      (parallelStep substitutionBoundary conditionalDiamond closedStar closedNormal atomShape
        nonClaim transports routes provenance localName : BHist) →
      ParallelConfluenceAuditUp
  deriving DecidableEq

def parallelConfluenceAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: parallelConfluenceAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: parallelConfluenceAuditEncodeBHist h

def parallelConfluenceAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (parallelConfluenceAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (parallelConfluenceAuditDecodeBHist tail)

private theorem parallelConfluenceAuditDecode_encode_bhist :
    ∀ h : BHist, parallelConfluenceAuditDecodeBHist
      (parallelConfluenceAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def parallelConfluenceAuditToEventFlow : ParallelConfluenceAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond closedStar
      closedNormal atomShape nonClaim transports routes provenance localName =>
      [[BMark.b0],
        parallelConfluenceAuditEncodeBHist parallelStep,
        [BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist substitutionBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist conditionalDiamond,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist closedStar,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist closedNormal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist atomShape,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist nonClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        parallelConfluenceAuditEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        parallelConfluenceAuditEncodeBHist localName]

def parallelConfluenceAuditFromEventFlow : EventFlow → Option ParallelConfluenceAuditUp
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
                      | conditionalDiamond :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | closedStar :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | closedNormal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | atomShape :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nonClaim :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transports :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | localName ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ParallelConfluenceAuditUp.mk
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    parallelStep)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    substitutionBoundary)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    conditionalDiamond)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    closedStar)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    closedNormal)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    atomShape)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    nonClaim)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    transports)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    routes)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    provenance)
                                                                                                  (parallelConfluenceAuditDecodeBHist
                                                                                                    localName))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem parallelConfluenceAudit_round_trip :
    ∀ x : ParallelConfluenceAuditUp,
      parallelConfluenceAuditFromEventFlow (parallelConfluenceAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parallelStep substitutionBoundary conditionalDiamond closedStar closedNormal atomShape
      nonClaim transports routes provenance localName =>
      change
        some
          (ParallelConfluenceAuditUp.mk
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist parallelStep))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist substitutionBoundary))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist conditionalDiamond))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist closedStar))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist closedNormal))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist atomShape))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist nonClaim))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist transports))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist routes))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist provenance))
            (parallelConfluenceAuditDecodeBHist
              (parallelConfluenceAuditEncodeBHist localName))) =
          some
            (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond
              closedStar closedNormal atomShape nonClaim transports routes provenance localName)
      rw [parallelConfluenceAuditDecode_encode_bhist parallelStep,
        parallelConfluenceAuditDecode_encode_bhist substitutionBoundary,
        parallelConfluenceAuditDecode_encode_bhist conditionalDiamond,
        parallelConfluenceAuditDecode_encode_bhist closedStar,
        parallelConfluenceAuditDecode_encode_bhist closedNormal,
        parallelConfluenceAuditDecode_encode_bhist atomShape,
        parallelConfluenceAuditDecode_encode_bhist nonClaim,
        parallelConfluenceAuditDecode_encode_bhist transports,
        parallelConfluenceAuditDecode_encode_bhist routes,
        parallelConfluenceAuditDecode_encode_bhist provenance,
        parallelConfluenceAuditDecode_encode_bhist localName]

private theorem parallelConfluenceAuditToEventFlow_injective {x y : ParallelConfluenceAuditUp} :
    parallelConfluenceAuditToEventFlow x = parallelConfluenceAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      parallelConfluenceAuditFromEventFlow (parallelConfluenceAuditToEventFlow x) =
        parallelConfluenceAuditFromEventFlow (parallelConfluenceAuditToEventFlow y) :=
    congrArg parallelConfluenceAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (parallelConfluenceAudit_round_trip x).symm
      (Eq.trans hread (parallelConfluenceAudit_round_trip y)))

instance parallelConfluenceAuditBHistCarrier : BHistCarrier ParallelConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := parallelConfluenceAuditToEventFlow
  fromEventFlow := parallelConfluenceAuditFromEventFlow

instance parallelConfluenceAuditChapterTasteGate :
    ChapterTasteGate ParallelConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change parallelConfluenceAuditFromEventFlow (parallelConfluenceAuditToEventFlow x) = some x
    exact parallelConfluenceAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (parallelConfluenceAuditToEventFlow_injective heq)

instance parallelConfluenceAuditFieldFaithful :
    FieldFaithful ParallelConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond
        closedStar closedNormal atomShape nonClaim transports routes provenance localName =>
        [parallelStep, substitutionBoundary, conditionalDiamond, closedStar, closedNormal,
          atomShape, nonClaim, transports, routes, provenance, localName]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk parallelStep₁ substitutionBoundary₁ conditionalDiamond₁ closedStar₁ closedNormal₁
        atomShape₁ nonClaim₁ transports₁ routes₁ provenance₁ localName₁ =>
        cases y with
        | mk parallelStep₂ substitutionBoundary₂ conditionalDiamond₂ closedStar₂ closedNormal₂
            atomShape₂ nonClaim₂ transports₂ routes₂ provenance₂ localName₂ =>
            cases h
            rfl

instance parallelConfluenceAuditNontrivial : Nontrivial ParallelConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ParallelConfluenceAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ParallelConfluenceAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem ParallelConfluenceAuditTasteGate_single_carrier_alignment :
    parallelConfluenceAuditFromEventFlow
        (parallelConfluenceAuditToEventFlow
          (ParallelConfluenceAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty)) =
      some
        (ParallelConfluenceAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact parallelConfluenceAudit_round_trip
    (ParallelConfluenceAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

theorem ParallelConfluenceAudit_conditional_bridge_rows
    {P S D C Nm At No H R L G P' S' D' C' Nm' At' No' H' R' L' G' : BHist}
    (sameDisplay :
      parallelConfluenceAuditToEventFlow
          (ParallelConfluenceAuditUp.mk P S D C Nm At No H R L G) =
        parallelConfluenceAuditToEventFlow
          (ParallelConfluenceAuditUp.mk P' S' D' C' Nm' At' No' H' R' L' G'))
    (conditionalRoute : Cont S D C)
    (closedStarRoute : Cont D C R) :
    hsame S S' ∧ hsame D D' ∧ hsame C C' ∧ hsame Nm Nm' ∧ hsame At At' ∧
      Cont S' D' C' ∧ Cont D' C' R' := by
  -- BEDC touchpoint anchor: BHist BMark
  have carrierEq :
      ParallelConfluenceAuditUp.mk P S D C Nm At No H R L G =
        ParallelConfluenceAuditUp.mk P' S' D' C' Nm' At' No' H' R' L' G' :=
    parallelConfluenceAuditToEventFlow_injective sameDisplay
  cases carrierEq
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · exact conditionalRoute
            · exact closedStarRoute

theorem ParallelConfluenceAudit_conditional_bridge_route_closed
    {parallelStep substitutionBoundary conditionalDiamond closedStar closedNormal atomShape nonClaim
      transports routes provenance localName substitutionRead diamondRead starRead : BHist} :
    UnaryHistory parallelStep ->
      UnaryHistory substitutionBoundary ->
        UnaryHistory conditionalDiamond ->
          UnaryHistory closedStar ->
            Cont parallelStep substitutionBoundary substitutionRead ->
              Cont substitutionRead conditionalDiamond diamondRead ->
                Cont diamondRead closedStar starRead ->
                  UnaryHistory substitutionRead ∧
                    UnaryHistory diamondRead ∧
                      UnaryHistory starRead ∧
                        parallelConfluenceAuditFromEventFlow
                            (parallelConfluenceAuditToEventFlow
                              (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary
                                conditionalDiamond closedStar closedNormal atomShape nonClaim
                                transports routes provenance localName)) =
                          some
                            (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary
                              conditionalDiamond closedStar closedNormal atomShape nonClaim
                              transports routes provenance localName) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro unaryParallel unarySubstitution unaryDiamond unaryStar routeSubstitution routeDiamond
    routeStar
  have unarySubstitutionRead : UnaryHistory substitutionRead :=
    unary_cont_closed unaryParallel unarySubstitution routeSubstitution
  have unaryDiamondRead : UnaryHistory diamondRead :=
    unary_cont_closed unarySubstitutionRead unaryDiamond routeDiamond
  have unaryStarRead : UnaryHistory starRead :=
    unary_cont_closed unaryDiamondRead unaryStar routeStar
  constructor
  · exact unarySubstitutionRead
  · constructor
    · exact unaryDiamondRead
    · constructor
      · exact unaryStarRead
      · exact
          parallelConfluenceAudit_round_trip
            (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond
              closedStar closedNormal atomShape nonClaim transports routes provenance localName)

end BEDC.Derived.ParallelConfluenceAuditUp
