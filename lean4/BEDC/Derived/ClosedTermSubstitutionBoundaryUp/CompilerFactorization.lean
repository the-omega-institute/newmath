import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryCompilerFactorization [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              Cont compilerRead audit nameRead ->
                PkgSig bundle nameRead pkg ->
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory compilerRead ∧ UnaryHistory nameRead ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit compilerRead ∧
                          Cont compilerRead audit nameRead ∧ PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditCompilerRead compilerReadAuditNameRead nameReadPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompilerRead
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed compilerReadUnary auditUnary compilerReadAuditNameRead
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, compilerReadUnary, nameReadUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditCompilerRead,
      compilerReadAuditNameRead, nameReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
