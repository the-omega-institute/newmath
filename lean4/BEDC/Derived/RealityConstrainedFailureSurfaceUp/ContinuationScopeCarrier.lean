import BEDC.Derived.RealityConstrainedFailureSurfaceUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealityConstrainedFailureSurfaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealityConstrainedFailureSurfaceCarrier_continuation_scope
    {O D K U L H C P N scopedRead replayRead : BHist} :
    RealityConstrainedFailureSurfaceUp →
      UnaryHistory U →
        UnaryHistory C →
          UnaryHistory P →
            Cont U C scopedRead →
              Cont scopedRead P replayRead →
                UnaryHistory scopedRead ∧
                  UnaryHistory replayRead ∧
                    Cont U C scopedRead ∧
                      Cont scopedRead P replayRead ∧
                        ∃ carrier : RealityConstrainedFailureSurfaceUp,
                          carrier =
                            RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro _carrier unaryU unaryC unaryP scopeRoute replayRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed unaryU unaryC scopeRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed scopedUnary unaryP replayRoute
  exact
    ⟨scopedUnary, replayUnary, scopeRoute, replayRoute,
      RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N, rfl⟩

end BEDC.Derived.RealityConstrainedFailureSurfaceUp
