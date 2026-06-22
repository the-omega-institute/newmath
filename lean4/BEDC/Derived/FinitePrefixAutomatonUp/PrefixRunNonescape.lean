import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_prefix_run_nonescape
    {Q q0 A T W R E H C P N transitionRead endpointRead acceptanceRead : BHist} :
    UnaryHistory T →
      UnaryHistory W →
        UnaryHistory C →
          UnaryHistory E →
            UnaryHistory A →
              Cont T W transitionRead →
                Cont transitionRead C endpointRead →
                  Cont E A acceptanceRead →
                    List.Mem (finitePrefixAutomatonEncodeBHist Q)
                        (finitePrefixAutomatonToEventFlow
                          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                      List.Mem (finitePrefixAutomatonEncodeBHist T)
                        (finitePrefixAutomatonToEventFlow
                          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                      List.Mem (finitePrefixAutomatonEncodeBHist W)
                        (finitePrefixAutomatonToEventFlow
                          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                      UnaryHistory transitionRead ∧ UnaryHistory endpointRead ∧
                        UnaryHistory acceptanceRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro transitionUnary wordUnary replayUnary endpointUnary acceptingUnary transitionRoute
    endpointRoute acceptanceRoute
  have statesDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist Q)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    exact List.Mem.head _
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
  have transitionReadUnary : UnaryHistory transitionRead :=
    unary_cont_closed transitionUnary wordUnary transitionRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed transitionReadUnary replayUnary endpointRoute
  have acceptanceReadUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed endpointUnary acceptingUnary acceptanceRoute
  exact
    ⟨statesDisplayed, transitionDisplayed, wordDisplayed, transitionReadUnary,
      endpointReadUnary, acceptanceReadUnary⟩

end BEDC.Derived.FinitePrefixAutomatonUp
