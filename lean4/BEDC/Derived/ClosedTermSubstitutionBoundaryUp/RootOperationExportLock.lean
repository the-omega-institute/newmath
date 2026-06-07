import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.RootOperationReadbackLock

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootOperationExportLock [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer rootRoute shiftRead
      substitutionRead operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitution ledger audit ->
              Cont substitutionRead audit operationRead ->
                Cont ledger audit route ->
                  Cont route audit consumer ->
                    Cont consumer route rootRoute ->
                      PkgSig bundle operationRead pkg ->
                        PkgSig bundle rootRoute pkg ->
                          hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                            UnaryHistory ledger ∧ UnaryHistory audit ∧
                              UnaryHistory operationRead ∧ UnaryHistory rootRoute ∧
                                Cont shift substitution ledger ∧
                                  Cont substitution ledger audit ∧
                                    Cont substitutionRead audit operationRead ∧
                                      Cont consumer route rootRoute ∧
                                        PkgSig bundle operationRead pkg ∧
                                          PkgSig bundle rootRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead
    shiftSubstitutionLedger substitutionLedgerAudit substitutionReadAuditOperation
    ledgerAuditRoute routeAuditConsumer consumerRouteRoot operationPkg rootPkg
  obtain ⟨sameShiftRead, sameSubstitutionRead, _sourceUnary, _shiftReadUnary,
    substitutionReadUnary⟩ :=
    ClosedTermSubstitutionBoundarySourceClosednessAdmission classifier sourceValueShiftRead
      shiftReadDepthSubstitutionRead
  obtain ⟨_sourceUnary, _valueUnary, _depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary ledgerUnary substitutionLedgerAudit
  have operationUnary : UnaryHistory operationRead :=
    unary_cont_closed substitutionReadUnary auditUnary substitutionReadAuditOperation
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have rootUnary : UnaryHistory rootRoute :=
    unary_cont_closed consumerUnary routeUnary consumerRouteRoot
  exact
    ⟨sameShiftRead, sameSubstitutionRead, ledgerUnary, auditUnary, operationUnary,
      rootUnary, shiftSubstitutionLedger, substitutionLedgerAudit,
      substitutionReadAuditOperation, consumerRouteRoot, operationPkg, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
