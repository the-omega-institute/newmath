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

theorem ClosedTermSubstitutionBoundaryRecursorAuditRoute [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route recursorBoundary consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit recursorBoundary ->
              Cont recursorBoundary audit consumer ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory recursorBoundary ∧ UnaryHistory consumer ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit recursorBoundary ∧
                          Cont recursorBoundary audit consumer ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRecursorBoundary recursorBoundaryAuditConsumer consumerPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have recursorBoundaryUnary : UnaryHistory recursorBoundary :=
    unary_cont_closed routeUnary auditUnary routeAuditRecursorBoundary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed recursorBoundaryUnary auditUnary recursorBoundaryAuditConsumer
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, recursorBoundaryUnary, consumerUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute,
      routeAuditRecursorBoundary, recursorBoundaryAuditConsumer, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
