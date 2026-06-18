import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_prefix_run_determinacy {q0 W R R' H E E' : BHist} :
    UnaryHistory q0 ->
      UnaryHistory W ->
        UnaryHistory H ->
          Cont q0 W R ->
            Cont q0 W R' ->
              Cont R H E ->
                Cont R' H E' ->
                  hsame R R' ∧ UnaryHistory R ∧ UnaryHistory R' ∧ UnaryHistory E ∧
                    UnaryHistory E' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro q0Unary wUnary hUnary route route' endpointRoute endpointRoute'
  have sameRuns : hsame R R' :=
    cont_deterministic route route'
  have runUnary : UnaryHistory R :=
    unary_cont_closed q0Unary wUnary route
  have runUnary' : UnaryHistory R' :=
    unary_cont_closed q0Unary wUnary route'
  have endpointUnary : UnaryHistory E :=
    unary_cont_closed runUnary hUnary endpointRoute
  have endpointUnary' : UnaryHistory E' :=
    unary_cont_closed runUnary' hUnary endpointRoute'
  exact ⟨sameRuns, runUnary, runUnary', endpointUnary, endpointUnary'⟩

end BEDC.Derived.FinitePrefixAutomatonUp
