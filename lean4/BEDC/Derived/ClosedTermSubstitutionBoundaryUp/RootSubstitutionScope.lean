import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootSubstitutionScope [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route substitutionScope rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont value substitution substitutionScope ->
        Cont shift substitution ledger ->
          Cont substitution depth audit ->
            Cont ledger audit route ->
              Cont route audit rootRead ->
                PkgSig bundle rootRead pkg ->
                  UnaryHistory substitutionScope ∧ UnaryHistory ledger ∧ UnaryHistory audit ∧
                    UnaryHistory route ∧ UnaryHistory rootRead ∧
                      Cont value substitution substitutionScope ∧
                        Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                          Cont ledger audit route ∧ Cont route audit rootRead ∧
                            PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier valueSubstitutionScope shiftSubstitutionLedger substitutionDepthAudit
    ledgerAuditRoute routeAuditRoot rootPkg
  obtain ⟨_sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have substitutionScopeUnary : UnaryHistory substitutionScope :=
    unary_cont_closed valueUnary substitutionUnary valueSubstitutionScope
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  exact
    ⟨substitutionScopeUnary, ledgerUnary, auditUnary, routeUnary, rootUnary,
      valueSubstitutionScope, shiftSubstitutionLedger, substitutionDepthAudit,
      ledgerAuditRoute, routeAuditRoot, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
