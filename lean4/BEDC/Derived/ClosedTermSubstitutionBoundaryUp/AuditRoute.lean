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

theorem ClosedTermSubstitutionBoundaryAuditRoute [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont audit route auditRead ->
                PkgSig bundle auditRead pkg ->
                  UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory auditRead ∧
                    Cont ledger audit route ∧ Cont route audit consumer ∧
                      Cont audit route auditRead ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer auditRouteRead auditReadPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have _consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary routeUnary auditRouteRead
  exact
    ⟨auditUnary, routeUnary, auditReadUnary, ledgerAuditRoute, routeAuditConsumer,
      auditRouteRead, auditReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
