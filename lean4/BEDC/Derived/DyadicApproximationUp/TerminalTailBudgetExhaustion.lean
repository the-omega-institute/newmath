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

theorem DyadicApproximationCarrier_terminal_tail_budget_exhaustion [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell validatedEnclosure sealRow tailBudget
      diagonalRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance meshCell ->
                    Cont meshCell terminalProvenance validatedEnclosure ->
                      Cont terminalLedger terminalProvenance sealRow ->
                        Cont sealRow terminalProvenance tailBudget ->
                          Cont terminalWindow sealRow diagonalRead ->
                            Cont tailBudget diagonalRead budgetRead ->
                              PkgSig bundle tailBudget pkg ->
                                PkgSig bundle diagonalRead pkg ->
                                  PkgSig bundle budgetRead pkg ->
                                    DyadicApproximationCarrier terminalPrecision
                                        terminalEndpoint terminalWindow terminalLedger
                                        terminalProvenance bundle pkg ∧
                                      UnaryHistory meshCell ∧
                                        UnaryHistory validatedEnclosure ∧
                                          UnaryHistory sealRow ∧ UnaryHistory tailBudget ∧
                                            UnaryHistory diagonalRead ∧
                                              UnaryHistory budgetRead ∧
                                                hsame window terminalWindow ∧
                                                  PkgSig bundle budgetRead pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalWindowRoute terminalProvenanceRoute meshCellRoute enclosureRoute
  intro sealRoute tailBudgetRoute diagonalRoute budgetRoute _tailPkg _diagonalPkg budgetPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalWindowRoute terminalProvenanceRoute
  rcases transported with ⟨terminalCarrier, sameWindow⟩
  have terminalCarrierProof :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg := terminalCarrier
  obtain ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
    terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
    _terminalProvenanceRoute, _terminalPkg⟩ := terminalCarrier
  have meshCellUnary : UnaryHistory meshCell :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary meshCellRoute
  have validatedEnclosureUnary : UnaryHistory validatedEnclosure :=
    unary_cont_closed meshCellUnary terminalProvenanceUnary enclosureRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary sealRoute
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed sealUnary terminalProvenanceUnary tailBudgetRoute
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed terminalWindowUnary sealUnary diagonalRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailBudgetUnary diagonalUnary budgetRoute
  exact
    ⟨terminalCarrierProof, meshCellUnary, validatedEnclosureUnary, sealUnary, tailBudgetUnary,
      diagonalUnary, budgetUnary, sameWindow, budgetPkg⟩

end BEDC.Derived.DyadicApproximationUp
