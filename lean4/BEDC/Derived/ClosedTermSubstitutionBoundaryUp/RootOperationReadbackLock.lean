import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootOperationReadbackLock [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit shiftRead substitutionRead
      operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitution ledger audit ->
              Cont substitutionRead audit operationRead ->
                PkgSig bundle operationRead pkg ->
                  hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧
                      UnaryHistory operationRead ∧ Cont shift substitution ledger ∧
                        Cont substitution ledger audit ∧
                          Cont substitutionRead audit operationRead ∧
                            PkgSig bundle operationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead
    shiftSubstitutionLedger substitutionLedgerAudit substitutionReadAuditOperation
    operationPkg
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
  exact
    ⟨sameShiftRead, sameSubstitutionRead, ledgerUnary, auditUnary, operationUnary,
      shiftSubstitutionLedger, substitutionLedgerAudit, substitutionReadAuditOperation,
      operationPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
