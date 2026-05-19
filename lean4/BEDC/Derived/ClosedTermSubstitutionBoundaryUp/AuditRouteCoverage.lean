import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryAuditRouteCoverage [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route auditRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont audit route auditRead ->
              Cont route audit consumer ->
                PkgSig bundle auditRead pkg ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory auditRead ∧ UnaryHistory consumer ∧
                        Cont ledger audit route ∧ Cont audit route auditRead ∧
                          Cont route audit consumer ∧ PkgSig bundle auditRead pkg ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    auditRouteRead routeAuditConsumer auditReadPkg consumerPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary routeUnary auditRouteRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, auditReadUnary, consumerUnary,
      ledgerAuditRoute, auditRouteRead, routeAuditConsumer, auditReadPkg, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
