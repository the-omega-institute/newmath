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

theorem ClosedTermSubstitutionBoundaryObligationRouteTriad [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route operationAudit consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont shift ledger operationAudit ->
                Cont substitution audit operationAudit ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                      UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                        UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                          UnaryHistory operationAudit ∧ Cont source value shift ∧
                            Cont shift depth substitution ∧ Cont shift substitution ledger ∧
                              Cont substitution depth audit ∧ Cont ledger audit route ∧
                                Cont route audit consumer ∧ Cont shift ledger operationAudit ∧
                                  Cont substitution audit operationAudit ∧
                                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer shiftLedgerOperationAudit substitutionAuditOperationAudit consumerPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have operationAuditUnary : UnaryHistory operationAudit :=
    unary_cont_closed shiftUnary ledgerUnary shiftLedgerOperationAudit
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, operationAuditUnary, sourceValueShift,
      shiftDepthSubstitution, shiftSubstitutionLedger, substitutionDepthAudit,
      ledgerAuditRoute, routeAuditConsumer, shiftLedgerOperationAudit,
      substitutionAuditOperationAudit, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
