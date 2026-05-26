import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryConsumerAuditTriad [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer auditReplay auditTerminal
      closedSourceRead substitutionBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont audit route auditReplay ->
                Cont auditReplay consumer auditTerminal ->
                  Cont source value closedSourceRead ->
                    Cont substitution ledger substitutionBudget ->
                      PkgSig bundle auditTerminal pkg ->
                        UnaryHistory closedSourceRead ∧ UnaryHistory substitutionBudget ∧
                          UnaryHistory consumer ∧ UnaryHistory auditTerminal ∧
                            Cont source value closedSourceRead ∧
                              Cont substitution ledger substitutionBudget ∧
                                PkgSig bundle auditTerminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer auditRouteReplay replayConsumerTerminal sourceValueClosed
    substitutionLedgerBudget terminalPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
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
  have closedSourceUnary : UnaryHistory closedSourceRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have substitutionBudgetUnary : UnaryHistory substitutionBudget :=
    unary_cont_closed substitutionUnary ledgerUnary substitutionLedgerBudget
  exact
    ⟨closedSourceUnary, substitutionBudgetUnary, consumerUnary, auditTerminalUnary,
      sourceValueClosed, substitutionLedgerBudget, terminalPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
