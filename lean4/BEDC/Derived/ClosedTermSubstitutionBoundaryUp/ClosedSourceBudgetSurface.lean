import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosedSourceBudgetSurface [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                  UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                    UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit consumer ∧
                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, shiftSubstitutionLedger, substitutionDepthAudit,
      ledgerAuditRoute, routeAuditConsumer, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
