import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootCompilerRouteExhaustion [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              PkgSig bundle compilerRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row compilerRead ∧ UnaryHistory row)
                    (fun row : BHist => Cont route audit row ∧ PkgSig bundle compilerRead pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle compilerRead pkg)
                    hsame ∧
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory compilerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditCompilerRead compilerPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompilerRead
  have sourceCompiler :
      (fun row : BHist => hsame row compilerRead ∧ UnaryHistory row) compilerRead :=
    ⟨hsame_refl compilerRead, compilerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compilerRead ∧ UnaryHistory row)
          (fun row : BHist => Cont route audit row ∧ PkgSig bundle compilerRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle compilerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compilerRead sourceCompiler
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport routeAuditCompilerRead (hsame_symm source.left),
          compilerPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compilerPkg⟩
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, compilerUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
