import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryOperationRoute [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value ledger ->
        Cont value depth audit ->
          Cont shift substitution route ->
            Cont route audit operationRead ->
              PkgSig bundle operationRead pkg ->
                UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                  UnaryHistory operationRead ∧ Cont source value ledger ∧
                    Cont value depth audit ∧ Cont shift substitution route ∧
                      Cont route audit operationRead ∧ PkgSig bundle operationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceValueLedger valueDepthAudit shiftSubstitutionRoute
    routeAuditOperation operationPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary valueUnary sourceValueLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed valueUnary depthUnary valueDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionRoute
  have operationUnary : UnaryHistory operationRead :=
    unary_cont_closed routeUnary auditUnary routeAuditOperation
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, operationUnary, sourceValueLedger, valueDepthAudit,
      shiftSubstitutionRoute, routeAuditOperation, operationPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
