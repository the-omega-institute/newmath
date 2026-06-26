import BEDC.Derived.RademacherUp

namespace BEDC.Derived.RademacherUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RademacherCarrier_difference_window_obligation
    {L E D M A H C P N dyadicMetricRead lipschitzControlRead realRead replayRead : BHist} :
    RademacherCarrier L E D M A H C P N ->
      Cont D M dyadicMetricRead ->
        Cont L A lipschitzControlRead ->
          Cont dyadicMetricRead lipschitzControlRead realRead ->
            Cont realRead C replayRead ->
              UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory L ∧ UnaryHistory A ∧
                UnaryHistory E ∧ UnaryHistory realRead ∧ UnaryHistory replayRead ∧
                  hsame replayRead (append realRead C) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier dyadicMetricRoute lipschitzControlRoute realRoute replayRoute
  have finitePacket :=
    RademacherCarrier_finite_derivative_candidate_packet carrier dyadicMetricRoute
      lipschitzControlRoute realRoute
  have realUnary : UnaryHistory realRead := finitePacket.right.right.right
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed realUnary carrier.right.right.right.right.right.right.left replayRoute
  exact And.intro carrier.right.right.left
    (And.intro carrier.right.right.right.left
      (And.intro carrier.left
        (And.intro carrier.right.right.right.right.left
          (And.intro carrier.right.left
            (And.intro realUnary
              (And.intro replayUnary replayRoute))))))

end BEDC.Derived.RademacherUp
