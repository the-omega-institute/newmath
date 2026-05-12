import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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
