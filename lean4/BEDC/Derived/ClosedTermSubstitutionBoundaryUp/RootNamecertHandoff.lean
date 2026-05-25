import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootNamecertHandoff [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead auditReplay handoff :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              Cont audit route auditReplay ->
                Cont auditReplay compilerRead handoff ->
                  PkgSig bundle handoff pkg ->
                    SemanticNameCert (fun row : BHist => hsame row handoff)
                        (fun row : BHist =>
                          Cont auditReplay compilerRead row ∧ PkgSig bundle handoff pkg)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle handoff pkg)
                        hsame ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory compilerRead ∧ UnaryHistory auditReplay ∧
                          UnaryHistory handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditCompiler auditRouteReplay replayCompilerHandoff handoffPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompiler
  have auditReplayUnary : UnaryHistory auditReplay :=
    unary_cont_closed auditUnary routeUnary auditRouteReplay
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditReplayUnary compilerReadUnary replayCompilerHandoff
  have cert :
      SemanticNameCert (fun row : BHist => hsame row handoff)
          (fun row : BHist => Cont auditReplay compilerRead row ∧ PkgSig bundle handoff pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle handoff pkg) hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff (hsame_refl handoff)
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
      intro _row source
      exact
        ⟨cont_result_hsame_transport replayCompilerHandoff (hsame_symm source), handoffPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport handoffUnary (hsame_symm source), handoffPkg⟩
  }
  exact
    ⟨cert, ledgerUnary, auditUnary, routeUnary, compilerReadUnary, auditReplayUnary,
      handoffUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
