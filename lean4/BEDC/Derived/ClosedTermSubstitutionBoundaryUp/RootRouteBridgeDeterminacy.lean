import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootRouteBridgeDeterminacy [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route consumer rootRoute rootRoute'
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer route rootRoute ->
                Cont consumer route rootRoute' ->
                  Cont rootRoute ledger bridgeRead ->
                    PkgSig bundle bridgeRead pkg ->
                      hsame rootRoute rootRoute' ∧ UnaryHistory consumer ∧
                        UnaryHistory rootRoute ∧ UnaryHistory rootRoute' ∧
                          UnaryHistory bridgeRead ∧ Cont consumer route rootRoute ∧
                            Cont consumer route rootRoute' ∧
                              Cont rootRoute ledger bridgeRead ∧
                                PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteRoot consumerRouteRoot' rootLedgerBridge bridgePkg
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
  have rootUnary : UnaryHistory rootRoute :=
    unary_cont_closed consumerUnary routeUnary consumerRouteRoot
  have rootUnary' : UnaryHistory rootRoute' :=
    unary_cont_closed consumerUnary routeUnary consumerRouteRoot'
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed rootUnary ledgerUnary rootLedgerBridge
  have sameRoot : hsame rootRoute rootRoute' :=
    cont_deterministic consumerRouteRoot consumerRouteRoot'
  exact
    ⟨sameRoot, consumerUnary, rootUnary, rootUnary', bridgeUnary, consumerRouteRoot,
      consumerRouteRoot', rootLedgerBridge, bridgePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
