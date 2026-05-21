import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryLedgerRouteSeparation [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route
      auditRead operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            UnaryHistory audit ->
              Cont shift substitution operationRead ->
                Cont ledger audit route ->
                  Cont audit route auditRead ->
                    PkgSig bundle auditRead pkg ->
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory auditRead ∧ UnaryHistory operationRead ∧
                          Cont sourceClosed valueClosed ledger ∧
                            Cont shift substitution operationRead ∧
                              Cont ledger audit route ∧ Cont audit route auditRead ∧
                                PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier sourceValueClosed valueDepthClosed closednessLedger auditUnary
    shiftSubstitutionOperation ledgerAuditRoute auditRouteRead auditReadPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary closednessLedger
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionOperation
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary routeUnary auditRouteRead
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, auditReadUnary, operationReadUnary,
      closednessLedger, shiftSubstitutionOperation, ledgerAuditRoute, auditRouteRead,
      auditReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
