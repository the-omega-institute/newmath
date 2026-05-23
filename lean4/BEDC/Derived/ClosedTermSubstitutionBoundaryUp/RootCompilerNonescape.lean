import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootCompilerNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              PkgSig bundle compilerRead pkg ->
                SemanticNameCert (fun row : BHist => hsame row compilerRead)
                    (fun row : BHist => Cont route audit row ∧ PkgSig bundle compilerRead pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle compilerRead pkg)
                    hsame ∧
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory compilerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
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
  have cert :
      SemanticNameCert (fun row : BHist => hsame row compilerRead)
          (fun row : BHist => Cont route audit row ∧ PkgSig bundle compilerRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle compilerRead pkg) hsame := {
    core := {
      carrier_inhabited := Exists.intro compilerRead (hsame_refl compilerRead)
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
      exact And.intro
        (cont_result_hsame_transport routeAuditCompilerRead (hsame_symm source))
        compilerPkg
    ledger_sound := by
      intro _row source
      exact And.intro (unary_transport compilerUnary (hsame_symm source)) compilerPkg
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, compilerUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
