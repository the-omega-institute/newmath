import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootLedgerReadiness [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer auditReplay auditTerminal
      scopeTerminal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont audit route auditReplay ->
                Cont auditReplay consumer auditTerminal ->
                  Cont auditTerminal audit scopeTerminal ->
                    Cont scopeTerminal consumer publicRead ->
                      PkgSig bundle publicRead pkg ->
                        UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                          UnaryHistory consumer ∧ UnaryHistory auditReplay ∧
                            UnaryHistory auditTerminal ∧ UnaryHistory scopeTerminal ∧
                              UnaryHistory publicRead ∧
                                Cont scopeTerminal consumer publicRead ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer auditRouteReplay replayConsumerTerminal terminalAuditScope
    scopeConsumerPublic publicPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
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
  have scopeTerminalUnary : UnaryHistory scopeTerminal :=
    unary_cont_closed auditTerminalUnary auditUnary terminalAuditScope
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed scopeTerminalUnary consumerUnary scopeConsumerPublic
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, consumerUnary, auditReplayUnary,
      auditTerminalUnary, scopeTerminalUnary, publicReadUnary, scopeConsumerPublic, publicPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
