import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.HypothesisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem HypothesisTestDecisionCarrier_type_one_error_ledger
    {null reject budget ledger endpoint : BHist} :
    UnaryHistory null -> UnaryHistory reject -> UnaryHistory budget ->
      Cont reject budget ledger -> Cont null ledger endpoint ->
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ hsame ledger (append reject budget) ∧
          hsame endpoint (append null ledger) := by
  intro nullUnary rejectUnary budgetUnary ledgerRow endpointRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed rejectUnary budgetUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed nullUnary ledgerUnary endpointRow
  exact ⟨ledgerUnary, endpointUnary, ledgerRow, endpointRow⟩

end BEDC.Derived.HypothesisUp
