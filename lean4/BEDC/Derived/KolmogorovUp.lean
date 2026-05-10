import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.KolmogorovUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem KolmogorovBudgetMonotonicity_budget_extension
    {description budget budget' decoder admissible admissible' trace trace' readback readback'
      ledger ledger' : BHist} :
    UnaryHistory description -> UnaryHistory budget -> UnaryHistory decoder -> hsame budget budget' ->
      Cont description budget admissible -> Cont description budget' admissible' ->
        Cont decoder admissible trace -> Cont decoder admissible' trace' ->
          Cont trace budget readback -> Cont trace' budget' readback' ->
            Cont description readback ledger -> Cont description readback' ledger' ->
              UnaryHistory budget' ∧ UnaryHistory admissible ∧ UnaryHistory admissible' ∧
                UnaryHistory trace ∧ UnaryHistory trace' ∧ UnaryHistory readback ∧
                  UnaryHistory readback' ∧ UnaryHistory ledger ∧ UnaryHistory ledger' ∧
                    hsame admissible admissible' ∧ hsame trace trace' ∧
                      hsame readback readback' ∧ hsame ledger ledger' := by
  intro descriptionUnary budgetUnary decoderUnary sameBudget admissibleRow admissibleRow'
  intro traceRow traceRow' readbackRow readbackRow' ledgerRow ledgerRow'
  have budgetUnary' : UnaryHistory budget' :=
    unary_transport budgetUnary sameBudget
  have admissibleUnary : UnaryHistory admissible :=
    unary_cont_closed descriptionUnary budgetUnary admissibleRow
  have admissibleUnary' : UnaryHistory admissible' :=
    unary_cont_closed descriptionUnary budgetUnary' admissibleRow'
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed decoderUnary admissibleUnary traceRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed decoderUnary admissibleUnary' traceRow'
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed traceUnary budgetUnary readbackRow
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed traceUnary' budgetUnary' readbackRow'
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed descriptionUnary readbackUnary ledgerRow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed descriptionUnary readbackUnary' ledgerRow'
  have sameAdmissible : hsame admissible admissible' :=
    cont_respects_hsame (hsame_refl description) sameBudget admissibleRow admissibleRow'
  have sameTrace : hsame trace trace' :=
    cont_respects_hsame (hsame_refl decoder) sameAdmissible traceRow traceRow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameTrace sameBudget readbackRow readbackRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl description) sameReadback ledgerRow ledgerRow'
  exact
    ⟨budgetUnary', admissibleUnary, admissibleUnary', traceUnary, traceUnary', readbackUnary,
      readbackUnary', ledgerUnary, ledgerUnary', sameAdmissible, sameTrace, sameReadback,
      sameLedger⟩

end BEDC.Derived.KolmogorovUp
