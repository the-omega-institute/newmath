import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryAuditNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route operationRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit operationRead ->
              Cont operationRead ledger auditRead ->
                PkgSig bundle auditRead pkg ->
                  UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory operationRead ∧
                    UnaryHistory auditRead ∧ Cont ledger audit route ∧
                      Cont route audit operationRead ∧ Cont operationRead ledger auditRead ∧
                        PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditOperation operationLedgerAuditRead auditPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have operationUnary : UnaryHistory operationRead :=
    unary_cont_closed routeUnary auditUnary routeAuditOperation
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed operationUnary ledgerUnary operationLedgerAuditRead
  exact
    ⟨auditUnary, routeUnary, operationUnary, auditReadUnary, ledgerAuditRoute,
      routeAuditOperation, operationLedgerAuditRead, auditPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
