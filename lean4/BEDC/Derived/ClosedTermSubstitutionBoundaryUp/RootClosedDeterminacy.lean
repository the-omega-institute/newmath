import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.ClosedValueRouteDeterminacy
import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.ConsumerLedgerExhaustion

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootClosedDeterminacy [AskSetup] [PackageSetup]
    {source value depth shift substitution valueReadA valueReadB substitutionReadA
      substitutionReadB ledger audit route consumer ledgerConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont value depth valueReadA ->
        Cont value depth valueReadB ->
          Cont shift valueReadA substitutionReadA ->
            Cont shift valueReadB substitutionReadB ->
              Cont shift substitution ledger ->
                Cont substitution depth audit ->
                  Cont ledger audit route ->
                    Cont route audit consumer ->
                      Cont ledger consumer ledgerConsumer ->
                        PkgSig bundle consumer pkg ->
                          PkgSig bundle ledgerConsumer pkg ->
                            hsame valueReadA valueReadB ∧
                              hsame substitutionReadA substitutionReadB ∧
                                UnaryHistory ledgerConsumer ∧
                                  Cont ledger consumer ledgerConsumer ∧
                                    PkgSig bundle ledgerConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro classifier valueDepthReadA valueDepthReadB shiftValueReadA shiftValueReadB
    shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute routeAuditConsumer
    ledgerConsumerRoute consumerPkg ledgerConsumerPkg
  obtain ⟨sameValueRead, sameSubstitutionRead, _valueReadAUnary, _valueReadBUnary,
    _substitutionReadAUnary, _substitutionReadBUnary⟩ :=
    ClosedTermSubstitutionBoundaryClosedValueRouteDeterminacy
      classifier valueDepthReadA valueDepthReadB shiftValueReadA shiftValueReadB
  obtain ⟨_ledgerUnary, _auditUnary, _routeUnary, _consumerUnary, ledgerConsumerUnary,
    ledgerConsumerRoute', ledgerConsumerPkg'⟩ :=
    ClosedTermSubstitutionBoundaryConsumerLedgerExhaustion
      classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute routeAuditConsumer
      ledgerConsumerRoute consumerPkg ledgerConsumerPkg
  exact
    ⟨sameValueRead, sameSubstitutionRead, ledgerConsumerUnary, ledgerConsumerRoute',
      ledgerConsumerPkg'⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
