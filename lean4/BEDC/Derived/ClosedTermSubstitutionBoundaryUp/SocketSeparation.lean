import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySocketSeparation [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer metacicConsumer socketRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer route metacicConsumer ->
                Cont metacicConsumer audit socketRead ->
                  PkgSig bundle consumer pkg ->
                    PkgSig bundle socketRead pkg ->
                      UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                        UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                          UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                            UnaryHistory metacicConsumer ∧ UnaryHistory socketRead ∧
                              Cont consumer route metacicConsumer ∧
                                Cont metacicConsumer audit socketRead ∧
                                  PkgSig bundle consumer pkg ∧
                                    PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteMetacic metacicAuditSocket consumerPkg socketPkg
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
  have metacicUnary : UnaryHistory metacicConsumer :=
    unary_cont_closed consumerUnary routeUnary consumerRouteMetacic
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed metacicUnary auditUnary metacicAuditSocket
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, metacicUnary, socketUnary,
      consumerRouteMetacic, metacicAuditSocket, consumerPkg, socketPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
