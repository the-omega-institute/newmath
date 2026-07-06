import BEDC.Derived.ParallelConfluenceAuditUp.TasteGate

namespace BEDC.Derived.ParallelConfluenceAuditUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

private theorem ParallelConfluenceAudit_residual_premise_retention_decode_aux :
    ∀ h : BHist,
      parallelConfluenceAuditDecodeBHist (parallelConfluenceAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

theorem ParallelConfluenceAudit_residual_premise_retention
    {parallelStep substitutionBoundary conditionalDiamond closedStar closedNormal atomShape nonClaim
      transports routes provenance localName substitutionRead diamondRead starRead premiseRead : BHist} :
    UnaryHistory parallelStep →
      UnaryHistory substitutionBoundary →
          UnaryHistory conditionalDiamond →
            UnaryHistory closedStar →
              UnaryHistory routes →
            Cont parallelStep substitutionBoundary substitutionRead →
              Cont substitutionRead conditionalDiamond diamondRead →
                Cont diamondRead closedStar starRead →
                  Cont substitutionBoundary routes premiseRead →
                    parallelConfluenceAuditFromEventFlow
                        (parallelConfluenceAuditToEventFlow
                          (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary
                            conditionalDiamond closedStar closedNormal atomShape nonClaim transports
                            routes provenance localName)) =
                      some
                        (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary
                          conditionalDiamond closedStar closedNormal atomShape nonClaim transports routes
                          provenance localName) ∧
                      UnaryHistory substitutionRead ∧ UnaryHistory diamondRead ∧
                        UnaryHistory starRead ∧ UnaryHistory premiseRead ∧
                          Cont substitutionBoundary routes premiseRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro parallelUnary substitutionUnary diamondUnary starUnary routesUnary substitutionRoute diamondRoute
    starRoute premiseRoute
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed parallelUnary substitutionUnary substitutionRoute
  have diamondReadUnary : UnaryHistory diamondRead :=
    unary_cont_closed substitutionReadUnary diamondUnary diamondRoute
  have starReadUnary : UnaryHistory starRead :=
    unary_cont_closed diamondReadUnary starUnary starRoute
  have premiseUnary : UnaryHistory premiseRead :=
    unary_cont_closed substitutionUnary routesUnary premiseRoute
  have roundTrip :
      parallelConfluenceAuditFromEventFlow
          (parallelConfluenceAuditToEventFlow
            (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond closedStar
              closedNormal atomShape nonClaim transports routes provenance localName)) =
        some
          (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond closedStar
            closedNormal atomShape nonClaim transports routes provenance localName) := by
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
          (ParallelConfluenceAuditUp.mk parallelStep substitutionBoundary conditionalDiamond closedStar
            closedNormal atomShape nonClaim transports routes provenance localName)
    rw [ParallelConfluenceAudit_residual_premise_retention_decode_aux parallelStep,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux substitutionBoundary,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux conditionalDiamond,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux closedStar,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux closedNormal,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux atomShape,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux nonClaim,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux transports,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux routes,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux provenance,
      ParallelConfluenceAudit_residual_premise_retention_decode_aux localName]
  exact
    ⟨roundTrip, substitutionReadUnary, diamondReadUnary, starReadUnary, premiseUnary,
      premiseRoute⟩

end BEDC.Derived.ParallelConfluenceAuditUp
