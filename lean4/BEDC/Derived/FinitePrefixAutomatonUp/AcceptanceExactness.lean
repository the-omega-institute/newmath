import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_acceptance_exactness_obligation
    {Q q0 A T W R E H C P N acceptanceRead : BHist} :
    UnaryHistory A →
      UnaryHistory E →
        Cont E A acceptanceRead →
          List.Mem (finitePrefixAutomatonEncodeBHist A)
              (finitePrefixAutomatonToEventFlow
                (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
            List.Mem (finitePrefixAutomatonEncodeBHist E)
              (finitePrefixAutomatonToEventFlow
                (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
            UnaryHistory acceptanceRead ∧ Cont E A acceptanceRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro acceptingUnary endpointUnary acceptanceRoute
  have acceptingDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist A)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have endpointDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist E)
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
    exact List.Mem.head _
  have acceptanceUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed endpointUnary acceptingUnary acceptanceRoute
  exact ⟨acceptingDisplayed, endpointDisplayed, acceptanceUnary, acceptanceRoute⟩

end BEDC.Derived.FinitePrefixAutomatonUp
