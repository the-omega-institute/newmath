import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryConsumerLedgerExhaustion [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer ledgerConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont ledger consumer ledgerConsumer ->
                PkgSig bundle consumer pkg ->
                  PkgSig bundle ledgerConsumer pkg ->
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory consumer ∧ UnaryHistory ledgerConsumer ∧
                        Cont ledger consumer ledgerConsumer ∧ PkgSig bundle ledgerConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer ledgerConsumerRoute _consumerPkg ledgerConsumerPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have ledgerConsumerUnary : UnaryHistory ledgerConsumer :=
    unary_cont_closed ledgerUnary consumerUnary ledgerConsumerRoute
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, consumerUnary, ledgerConsumerUnary,
      ledgerConsumerRoute, ledgerConsumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
