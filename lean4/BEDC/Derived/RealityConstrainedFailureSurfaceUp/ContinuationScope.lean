import BEDC.Derived.RealityConstrainedFailureSurfaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedFailureSurfaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealityConstrainedFailureSurfaceUp_continuation_scope
    {O D K U L H C P N scopeRead replayRead : BHist} :
    Cont U C scopeRead →
      Cont scopeRead P replayRead →
        UnaryHistory U →
          UnaryHistory C →
            UnaryHistory P →
              ∃ packet : RealityConstrainedFailureSurfaceUp,
                packet = RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N ∧
                  UnaryHistory scopeRead ∧
                    UnaryHistory replayRead ∧
                      List.Mem (realityConstrainedFailureSurfaceEncodeBHist U)
                        (realityConstrainedFailureSurfaceToEventFlow packet) ∧
                        List.Mem (realityConstrainedFailureSurfaceEncodeBHist C)
                          (realityConstrainedFailureSurfaceToEventFlow packet) ∧
                          List.Mem (realityConstrainedFailureSurfaceEncodeBHist P)
                            (realityConstrainedFailureSurfaceToEventFlow packet) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro scopeRoute replayRoute uUnary cUnary pUnary
  let packet := RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed uUnary cUnary scopeRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed scopeReadUnary pUnary replayRoute
  refine ⟨packet, rfl, scopeReadUnary, replayReadUnary, ?_, ?_, ?_⟩
  · exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _ (List.Mem.head _)))))))))))))
  · exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _ (List.Mem.head _)))))))))))))))

end BEDC.Derived.RealityConstrainedFailureSurfaceUp
