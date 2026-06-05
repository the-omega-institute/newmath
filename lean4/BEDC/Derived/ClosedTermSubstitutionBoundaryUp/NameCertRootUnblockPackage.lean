import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNameCertRootUnblockPackage [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead auditReplay
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              Cont audit route auditReplay ->
                Cont auditReplay compilerRead handoff ->
                  PkgSig bundle handoff pkg ->
                    PkgSig bundle route pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row handoff)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row value ∨ hsame row depth ∨
                              hsame row ledger ∨ hsame row audit ∨ hsame row route ∨
                                hsame row handoff)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle handoff pkg ∧
                              PkgSig bundle route pkg)
                          hsame ∧ UnaryHistory ledger ∧ UnaryHistory audit ∧
                        UnaryHistory route ∧ UnaryHistory compilerRead ∧
                          UnaryHistory auditReplay ∧ UnaryHistory handoff := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditCompiler auditRouteReplay replayCompilerHandoff handoffPkg routePkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompiler
  have auditReplayUnary : UnaryHistory auditReplay :=
    unary_cont_closed auditUnary routeUnary auditRouteReplay
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditReplayUnary compilerUnary replayCompilerHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨ hsame row ledger ∨
              hsame row audit ∨ hsame row route ∨ hsame row handoff)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle handoff pkg ∧ PkgSig bundle route pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff (hsame_refl handoff)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source)))))
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport handoffUnary (hsame_symm source), handoffPkg, routePkg⟩
  }
  exact
    ⟨cert, ledgerUnary, auditUnary, routeUnary, compilerUnary, auditReplayUnary,
      handoffUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
