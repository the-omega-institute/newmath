import BEDC.Derived.DyadicApproximationUp.TerminalTailBudgetExhaustion

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_tail_budget_real_completion_route
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell validatedEnclosure sealRow tailBudget
      diagonalRead budgetRead completionRoute : BHist}
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
                              Cont budgetRead terminalProvenance completionRoute ->
                                PkgSig bundle tailBudget pkg ->
                                  PkgSig bundle diagonalRead pkg ->
                                    PkgSig bundle budgetRead pkg ->
                                      PkgSig bundle completionRoute pkg ->
                                        DyadicApproximationCarrier terminalPrecision
                                            terminalEndpoint terminalWindow terminalLedger
                                            terminalProvenance bundle pkg ∧
                                          UnaryHistory budgetRead ∧
                                            UnaryHistory completionRoute ∧
                                              PkgSig bundle completionRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance terminalWindowRoute
  intro terminalProvenanceRoute meshCellRoute enclosureRoute sealRoute tailBudgetRoute
  intro diagonalRoute budgetRoute completionRouteCont tailPkg diagonalPkg budgetPkg completionPkg
  have exhausted :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory validatedEnclosure ∧ UnaryHistory sealRow ∧
          UnaryHistory tailBudget ∧ UnaryHistory diagonalRead ∧ UnaryHistory budgetRead ∧
            hsame window terminalWindow ∧ PkgSig bundle budgetRead pkg :=
    DyadicApproximationCarrier_terminal_tail_budget_exhaustion carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalWindowRoute terminalProvenanceRoute
      meshCellRoute enclosureRoute sealRoute tailBudgetRoute diagonalRoute budgetRoute tailPkg
      diagonalPkg budgetPkg
  obtain ⟨terminalCarrier, _meshCellUnary, _validatedEnclosureUnary, _sealUnary,
    _tailBudgetUnary, _diagonalUnary, budgetUnary, _sameWindow, _budgetPkg⟩ := exhausted
  have terminalCarrierProof :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg := terminalCarrier
  obtain ⟨_terminalPrecisionUnary, _terminalEndpointUnary, _terminalWindowUnary,
    _terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
    _terminalProvenanceRoute, _terminalPkg⟩ := terminalCarrier
  have completionUnary : UnaryHistory completionRoute :=
    unary_cont_closed budgetUnary terminalProvenanceUnary completionRouteCont
  exact ⟨terminalCarrierProof, budgetUnary, completionUnary, completionPkg⟩

end BEDC.Derived.DyadicApproximationUp
