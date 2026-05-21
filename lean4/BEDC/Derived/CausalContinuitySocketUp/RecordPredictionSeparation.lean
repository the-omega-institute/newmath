import BEDC.Derived.CausalContinuitySocketUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CausalContinuitySocketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CausalContinuitySocket_record_prediction_separation
    {record prediction gate socket transport route provenance name recordRead gateRead : BHist} :
    Cont record prediction recordRead →
      Cont recordRead gate gateRead →
        UnaryHistory record →
          UnaryHistory prediction →
            UnaryHistory gate →
              ∃ packet : CausalContinuitySocketUp,
                packet =
                    CausalContinuitySocketUp.mk record prediction gate socket transport route
                      provenance name ∧
                  UnaryHistory recordRead ∧
                    UnaryHistory gateRead ∧
                      List.Mem (causalContinuitySocketEncodeBHist record)
                        (causalContinuitySocketToEventFlow packet) ∧
                        List.Mem (causalContinuitySocketEncodeBHist prediction)
                          (causalContinuitySocketToEventFlow packet) ∧
                          List.Mem (causalContinuitySocketEncodeBHist gate)
                            (causalContinuitySocketToEventFlow packet) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro recordRoute gateRoute recordUnary predictionUnary gateUnary
  let packet :=
    CausalContinuitySocketUp.mk record prediction gate socket transport route provenance name
  have recordReadUnary : UnaryHistory recordRead :=
    unary_cont_closed recordUnary predictionUnary recordRoute
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed recordReadUnary gateUnary gateRoute
  refine ⟨packet, rfl, recordReadUnary, gateReadUnary, ?_, ?_, ?_⟩
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

end BEDC.Derived.CausalContinuitySocketUp
