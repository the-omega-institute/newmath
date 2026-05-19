import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNameCertExportTotality [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer auditReplay auditTerminal
      scopeTerminal : BHist}
    {bundle : ProbeBundle BEDC.FKernel.Ask.ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont audit route auditReplay ->
                Cont auditReplay consumer auditTerminal ->
                  Cont auditTerminal audit scopeTerminal ->
                    PkgSig bundle scopeTerminal pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row scopeTerminal)
                          (fun row : BHist =>
                            Cont auditTerminal audit row ∧ PkgSig bundle scopeTerminal pkg)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle scopeTerminal pkg)
                          hsame ∧
                        UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                          UnaryHistory consumer ∧ UnaryHistory auditReplay ∧
                            UnaryHistory auditTerminal ∧ UnaryHistory scopeTerminal := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer auditRouteReplay replayConsumerTerminal terminalAuditScope scopePkg
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
  have sourceTerminal : (fun row : BHist => hsame row scopeTerminal) scopeTerminal :=
    hsame_refl scopeTerminal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row scopeTerminal)
        (fun row : BHist => Cont auditTerminal audit row ∧ PkgSig bundle scopeTerminal pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle scopeTerminal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeTerminal sourceTerminal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro row source
      exact ⟨cont_result_hsame_transport terminalAuditScope (hsame_symm source), scopePkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport scopeTerminalUnary (hsame_symm source), scopePkg⟩
  }
  exact
    ⟨cert, ledgerUnary, auditUnary, routeUnary, consumerUnary, auditReplayUnary,
      auditTerminalUnary, scopeTerminalUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
