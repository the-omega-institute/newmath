import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryMetacicConsumerNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer metacicConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer route metacicConsumer ->
                PkgSig bundle consumer pkg ->
                  PkgSig bundle metacicConsumer pkg ->
                    UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                      UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                        UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                          UnaryHistory metacicConsumer ∧ Cont consumer route metacicConsumer ∧
                            PkgSig bundle consumer pkg ∧
                              PkgSig bundle metacicConsumer pkg ∧
                                SemanticNameCert
                                  (fun row : BHist =>
                                    ClosedTermSubstitutionBoundaryClassifier source value depth
                                      shift substitution ∧ hsame row consumer)
                                  (fun row : BHist =>
                                    Cont route audit row ∧ PkgSig bundle consumer pkg)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle consumer pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteMetacic consumerPkg metacicConsumerPkg
  have classifierWitness :
      ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution :=
    classifier
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerPacket :=
    ClosedTermSubstitutionBoundaryLedgerNonEscape classifierWitness shiftSubstitutionLedger
      substitutionDepthAudit ledgerAuditRoute routeAuditConsumer consumerPkg
  obtain ⟨ledgerUnary, auditUnary, routeUnary, consumerUnary, _shiftSubstitutionLedger,
    _substitutionDepthAudit, _ledgerAuditRoute, _routeAuditConsumer, _consumerPkg, cert⟩ :=
    ledgerPacket
  have metacicConsumerUnary : UnaryHistory metacicConsumer :=
    unary_cont_closed consumerUnary routeUnary consumerRouteMetacic
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, metacicConsumerUnary, consumerRouteMetacic,
      consumerPkg, metacicConsumerPkg, cert⟩

theorem ClosedTermSubstitutionBoundaryRootClosedBoundaryCut [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer rootCut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer ledger rootCut ->
                PkgSig bundle consumer pkg ->
                  PkgSig bundle rootCut pkg ->
                    UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                      UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                        UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                          UnaryHistory rootCut ∧ Cont consumer ledger rootCut ∧
                            PkgSig bundle consumer pkg ∧ PkgSig bundle rootCut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerLedgerRootCut consumerPkg rootCutPkg
  have consumerBoundary :=
    ClosedTermSubstitutionBoundaryConsumerBoundary classifier shiftSubstitutionLedger
      substitutionDepthAudit ledgerAuditRoute routeAuditConsumer consumerPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
    auditUnary, routeUnary, consumerUnary, _sourceValueShift, _shiftDepthSubstitution,
    _shiftSubstitutionLedger, _substitutionDepthAudit, _ledgerAuditRoute, _routeAuditConsumer,
    _consumerPkg⟩ := consumerBoundary
  have rootCutUnary : UnaryHistory rootCut :=
    unary_cont_closed consumerUnary ledgerUnary consumerLedgerRootCut
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, rootCutUnary, consumerLedgerRootCut, consumerPkg,
      rootCutPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
