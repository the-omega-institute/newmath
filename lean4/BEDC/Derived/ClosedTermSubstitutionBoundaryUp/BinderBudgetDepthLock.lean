import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryBinderBudgetDepthLock [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont shift substitution ledger ->
              Cont substitution depth audit ->
                Cont ledger audit route ->
                  Cont audit route auditRead ->
                    PkgSig bundle auditRead pkg ->
                      UnaryHistory depth ∧ UnaryHistory sourceClosed ∧
                        UnaryHistory valueClosed ∧ UnaryHistory ledger ∧
                          UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory auditRead ∧
                            Cont sourceClosed valueClosed ledger ∧
                              Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                                Cont ledger audit route ∧ Cont audit route auditRead ∧
                                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier sourceValueClosed valueDepthClosed closednessLedger shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute auditRouteRead auditReadPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary closednessLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary routeUnary auditRouteRead
  exact
    ⟨depthUnary, sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, routeUnary,
      auditReadUnary, closednessLedger, shiftSubstitutionLedger, substitutionDepthAudit,
      ledgerAuditRoute, auditRouteRead, auditReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
