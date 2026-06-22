import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_transition_exactness_obligation
    {Q q0 A T W R E H C P N transitionRead endpointRead : BHist} :
    UnaryHistory T →
      UnaryHistory W →
        UnaryHistory C →
          Cont T W transitionRead →
            Cont transitionRead C endpointRead →
              List.Mem (finitePrefixAutomatonEncodeBHist T)
                  (finitePrefixAutomatonToEventFlow
                    (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                List.Mem (finitePrefixAutomatonEncodeBHist W)
                  (finitePrefixAutomatonToEventFlow
                    (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                List.Mem (finitePrefixAutomatonEncodeBHist C)
                  (finitePrefixAutomatonToEventFlow
                    (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                UnaryHistory transitionRead ∧ UnaryHistory endpointRead ∧
                  Cont T W transitionRead ∧ Cont transitionRead C endpointRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro transitionUnary wordUnary replayUnary transitionRoute endpointRoute
  have transitionDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist T)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have wordDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist W)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have replayDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist C)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have transitionReadUnary : UnaryHistory transitionRead :=
    unary_cont_closed transitionUnary wordUnary transitionRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed transitionReadUnary replayUnary endpointRoute
  constructor
  · exact transitionDisplayed
  constructor
  · exact wordDisplayed
  constructor
  · exact replayDisplayed
  constructor
  · exact transitionReadUnary
  constructor
  · exact endpointReadUnary
  constructor
  · exact transitionRoute
  · exact endpointRoute

end BEDC.Derived.FinitePrefixAutomatonUp
