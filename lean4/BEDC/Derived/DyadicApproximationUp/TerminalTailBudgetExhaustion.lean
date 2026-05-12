import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_tail_budget_exhaustion_certificate
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance tailBudget terminalConsumer directConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalLedger terminalProvenance tailBudget ->
                    Cont terminalWindow tailBudget terminalConsumer ->
                      Cont (append terminalWindow terminalLedger) terminalProvenance
                          directConsumer ->
                        PkgSig bundle tailBudget pkg ->
                          PkgSig bundle terminalConsumer pkg ->
                            hsame terminalConsumer directConsumer ∧
                              UnaryHistory tailBudget ∧ UnaryHistory terminalConsumer ∧
                                UnaryHistory directConsumer ∧ PkgSig bundle tailBudget pkg ∧
                                  PkgSig bundle terminalConsumer pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance terminalWindowRoute
    terminalLedgerRoute tailBudgetRoute terminalConsumerRoute directConsumerRoute tailBudgetPkg
    terminalConsumerPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow terminalLedger
          terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint sameLedger
      sameProvenance terminalWindowRoute terminalLedgerRoute
  rcases transported with ⟨terminalCarrier, _sameWindow⟩
  rcases terminalCarrier with
    ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
      terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
      _terminalLedgerRoute, _terminalPkg⟩
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary tailBudgetRoute
  have terminalConsumerUnary : UnaryHistory terminalConsumer :=
    unary_cont_closed terminalWindowUnary tailBudgetUnary terminalConsumerRoute
  have terminalWindowLedgerUnary : UnaryHistory (append terminalWindow terminalLedger) :=
    unary_cont_closed terminalWindowUnary terminalLedgerUnary (cont_intro rfl)
  have directConsumerUnary : UnaryHistory directConsumer :=
    unary_cont_closed terminalWindowLedgerUnary terminalProvenanceUnary directConsumerRoute
  have terminalConsumerDirectRow :
      Cont (append terminalWindow terminalLedger) terminalProvenance terminalConsumer := by
    cases tailBudgetRoute
    cases terminalConsumerRoute
    exact (append_assoc terminalWindow terminalLedger terminalProvenance).symm
  have consumerSameDirect : hsame terminalConsumer directConsumer :=
    cont_deterministic terminalConsumerDirectRow directConsumerRoute
  exact
    ⟨consumerSameDirect, tailBudgetUnary, terminalConsumerUnary, directConsumerUnary,
      tailBudgetPkg, terminalConsumerPkg⟩

end BEDC.Derived.DyadicApproximationUp
