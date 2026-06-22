import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FinitePrefixAutomaton_endpoint_exactness_obligation
    {Q q0 A T W R E H C P N : BHist} :
    UnaryHistory R ->
      UnaryHistory H ->
        Cont R H E ->
          UnaryHistory E ∧
            List.Mem (finitePrefixAutomatonEncodeBHist E)
              (finitePrefixAutomatonToEventFlow
                (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro runUnary transportUnary endpointRoute
  have endpointUnary : UnaryHistory E :=
    unary_cont_closed runUnary transportUnary endpointRoute
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
  exact ⟨endpointUnary, endpointDisplayed⟩

end BEDC.Derived.FinitePrefixAutomatonUp
