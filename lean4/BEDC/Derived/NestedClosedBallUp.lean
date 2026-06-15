import BEDC.Derived.NestedClosedBallUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedClosedBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NestedClosedBallRegSeqRatCenterExtraction
    {M K F S R D E H C P N centerWindow dyadicRefinement realSeal : BHist} :
    Cont F S centerWindow ->
      Cont centerWindow R dyadicRefinement ->
        Cont dyadicRefinement D realSeal ->
          UnaryHistory F ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory centerWindow ∧ UnaryHistory dyadicRefinement ∧
                    UnaryHistory realSeal ∧ Cont F S centerWindow ∧
                      Cont centerWindow R dyadicRefinement ∧
                        Cont dyadicRefinement D realSeal ∧
                          TasteGate.NestedClosedBallTasteGate_single_carrier_alignment_fields
                              (TasteGate.NestedClosedBallUp.mk M K F S R D E H C P N) =
                            [M, K, F, S, R, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro filterStreamRoute streamReadbackRoute readbackDyadicRoute filterUnary streamUnary
    readbackUnary dyadicUnary
  have centerWindowUnary : UnaryHistory centerWindow :=
    unary_cont_closed filterUnary streamUnary filterStreamRoute
  have dyadicRefinementUnary : UnaryHistory dyadicRefinement :=
    unary_cont_closed centerWindowUnary readbackUnary streamReadbackRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicRefinementUnary dyadicUnary readbackDyadicRoute
  exact
    ⟨centerWindowUnary, dyadicRefinementUnary, realSealUnary, filterStreamRoute,
      streamReadbackRoute, readbackDyadicRoute, rfl⟩

end BEDC.Derived.NestedClosedBallUp
