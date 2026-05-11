import BEDC.Derived.LQRUp

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LQRFiniteControlCarrier_empty_horizon_backward_ledger
    {state control transition cost horizon estimator backward provenance endpoint : BHist} :
    LQRFiniteControlCarrier state control transition cost horizon estimator backward provenance
        endpoint ->
      hsame horizon BHist.Empty ->
        hsame endpoint provenance ∧ Cont provenance horizon endpoint ∧
          UnaryHistory provenance := by
  intro carrier emptyHorizon
  rcases carrier with
    ⟨stateUnary, controlUnary, costUnary, _horizonUnary, estimatorUnary, transitionRow,
      backwardRow, provenanceRow, endpointRow⟩
  have transitionUnary : UnaryHistory transition :=
    unary_cont_closed stateUnary controlUnary transitionRow
  have backwardUnary : UnaryHistory backward :=
    unary_cont_closed transitionUnary costUnary backwardRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed backwardUnary estimatorUnary provenanceRow
  have endpointSame : hsame endpoint provenance :=
    by
      cases emptyHorizon
      exact cont_right_unit_iff.mp endpointRow
  exact ⟨endpointSame, endpointRow, provenanceUnary⟩

end BEDC.Derived.LQRUp
