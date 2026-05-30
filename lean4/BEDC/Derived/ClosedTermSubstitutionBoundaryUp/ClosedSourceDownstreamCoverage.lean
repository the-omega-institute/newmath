import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosedSourceDownstreamCoverage [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route consumer
      auditReplay auditTerminal scopeTerminal closedSourceRead substitutionBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont shift substitution ledger ->
              Cont substitution depth audit ->
                Cont ledger audit route ->
                  Cont route audit consumer ->
                    Cont audit route auditReplay ->
                      Cont auditReplay consumer auditTerminal ->
                        Cont auditTerminal audit scopeTerminal ->
                          Cont source value closedSourceRead ->
                            Cont substitution ledger substitutionBudget ->
                              PkgSig bundle scopeTerminal pkg ->
                                UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                                  UnaryHistory ledger ∧ UnaryHistory audit ∧
                                    UnaryHistory route ∧ UnaryHistory consumer ∧
                                      UnaryHistory auditReplay ∧
                                        UnaryHistory auditTerminal ∧
                                          UnaryHistory scopeTerminal ∧
                                            UnaryHistory closedSourceRead ∧
                                              UnaryHistory substitutionBudget ∧
                                                Cont source value sourceClosed ∧
                                                  Cont value depth valueClosed ∧
                                                    Cont sourceClosed valueClosed ledger ∧
                                                      Cont shift substitution ledger ∧
                                                        Cont substitution depth audit ∧
                                                          Cont ledger audit route ∧
                                                            Cont route audit consumer ∧
                                                              Cont audit route auditReplay ∧
                                                                Cont auditReplay consumer
                                                                  auditTerminal ∧
                                                                  Cont auditTerminal audit
                                                                    scopeTerminal ∧
                                                                    Cont source value
                                                                      closedSourceRead ∧
                                                                      Cont substitution ledger
                                                                        substitutionBudget ∧
                                                                        PkgSig bundle
                                                                          scopeTerminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceValueClosed valueDepthClosed closedRowsLedger shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute routeAuditConsumer auditRouteReplay
    replayConsumerTerminal terminalAuditScope sourceValueRead substitutionLedgerBudget
    terminalPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary closedRowsLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have auditReplayUnary : UnaryHistory auditReplay :=
    unary_cont_closed auditUnary routeUnary auditRouteReplay
  have auditTerminalUnary : UnaryHistory auditTerminal :=
    unary_cont_closed auditReplayUnary consumerUnary replayConsumerTerminal
  have scopeTerminalUnary : UnaryHistory scopeTerminal :=
    unary_cont_closed auditTerminalUnary auditUnary terminalAuditScope
  have closedSourceReadUnary : UnaryHistory closedSourceRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueRead
  have substitutionBudgetUnary : UnaryHistory substitutionBudget :=
    unary_cont_closed substitutionUnary ledgerUnary substitutionLedgerBudget
  exact
    ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, routeUnary, consumerUnary,
      auditReplayUnary, auditTerminalUnary, scopeTerminalUnary, closedSourceReadUnary,
      substitutionBudgetUnary, sourceValueClosed, valueDepthClosed, closedRowsLedger,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      auditRouteReplay, replayConsumerTerminal, terminalAuditScope, sourceValueRead,
      substitutionLedgerBudget, terminalPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
