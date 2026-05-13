import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ParallelConfluenceAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
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

end BEDC.Derived.ParallelConfluenceAuditUp
