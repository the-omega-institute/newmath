import BEDC.Derived.DyadicApproximationUp.TerminalTailBudgetRealCompletionRoute

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_l10_real_completion_sibling_route
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell validatedEnclosure sealRow tailBudget
      diagonalRead budgetRead streamWindow regSeqReadback dyadicLedger realCompletionSeal
      completionRoute : BHist}
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
                              Cont terminalWindow terminalProvenance streamWindow ->
                                Cont streamWindow terminalProvenance regSeqReadback ->
                                  Cont regSeqReadback terminalProvenance dyadicLedger ->
                                    Cont dyadicLedger terminalProvenance realCompletionSeal ->
                                      Cont budgetRead terminalProvenance completionRoute ->
                                        PkgSig bundle tailBudget pkg ->
                                          PkgSig bundle diagonalRead pkg ->
                                            PkgSig bundle budgetRead pkg ->
                                              PkgSig bundle completionRoute pkg ->
                                                DyadicApproximationCarrier terminalPrecision
                                                    terminalEndpoint terminalWindow
                                                    terminalLedger terminalProvenance bundle
                                                    pkg ∧
                                                  UnaryHistory streamWindow ∧
                                                    UnaryHistory regSeqReadback ∧
                                                      UnaryHistory dyadicLedger ∧
                                                        UnaryHistory realCompletionSeal ∧
                                                          UnaryHistory completionRoute ∧
                                                            PkgSig bundle completionRoute pkg :=
  by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance terminalWindowRoute
  intro terminalProvenanceRoute meshCellRoute enclosureRoute sealRoute tailBudgetRoute
  intro diagonalRoute budgetRoute streamWindowRoute regSeqRoute dyadicLedgerRoute
  intro realCompletionSealRoute completionRouteCont tailPkg diagonalPkg budgetPkg completionPkg
  have terminalRoute :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory budgetRead ∧ UnaryHistory completionRoute ∧
          PkgSig bundle completionRoute pkg :=
    DyadicApproximationCarrier_terminal_tail_budget_real_completion_route carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalWindowRoute terminalProvenanceRoute
      meshCellRoute enclosureRoute sealRoute tailBudgetRoute diagonalRoute budgetRoute
      completionRouteCont tailPkg diagonalPkg budgetPkg completionPkg
  obtain ⟨terminalCarrier, _budgetUnary, completionUnary, completionPkgProof⟩ :=
    terminalRoute
  have terminalCarrierProof :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg :=
    terminalCarrier
  obtain ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary,
    terminalLedgerUnary, terminalProvenanceUnary, terminalWindowRouteProof,
    terminalProvenanceRouteProof, terminalPkg⟩ := terminalCarrierProof
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary streamWindowRoute
  have regSeqReadbackUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed streamWindowUnary terminalProvenanceUnary regSeqRoute
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed regSeqReadbackUnary terminalProvenanceUnary dyadicLedgerRoute
  have realCompletionSealUnary : UnaryHistory realCompletionSeal :=
    unary_cont_closed dyadicLedgerUnary terminalProvenanceUnary realCompletionSealRoute
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary,
        terminalLedgerUnary, terminalProvenanceUnary, terminalWindowRouteProof,
        terminalProvenanceRouteProof, terminalPkg⟩,
      streamWindowUnary, regSeqReadbackUnary, dyadicLedgerUnary, realCompletionSealUnary,
      completionUnary, completionPkgProof⟩

end BEDC.Derived.DyadicApproximationUp
