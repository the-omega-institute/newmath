import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySubstitutionBudgetTotality [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route consumer
      auditReplay auditTerminal scopeTerminal : BHist}
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
                          PkgSig bundle scopeTerminal pkg ->
                            UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                              UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                                UnaryHistory consumer ∧ UnaryHistory auditReplay ∧
                                  UnaryHistory auditTerminal ∧ UnaryHistory scopeTerminal ∧
                                    PkgSig bundle scopeTerminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceValueClosed valueDepthClosed sourceValueLedger
    shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute routeAuditConsumer
    auditRouteReplay replayConsumerTerminal terminalAuditScope scopePkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary sourceValueLedger
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
  exact
    ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, routeUnary,
      consumerUnary, auditReplayUnary, auditTerminalUnary, scopeTerminalUnary, scopePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
