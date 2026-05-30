import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryPacket_self_compile_route
    {source value depth shift substitution ledger audit selfCompileRead : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution →
      Cont shift substitution ledger →
        Cont substitution depth audit →
          Cont ledger audit selfCompileRead →
            UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory selfCompileRead ∧
              Cont source value shift ∧ Cont shift depth substitution ∧
                Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                  Cont ledger audit selfCompileRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have selfCompileUnary : UnaryHistory selfCompileRead :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  exact
    ⟨ledgerUnary, auditUnary, selfCompileUnary, sourceValueShift, shiftDepthSubstitution,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute⟩

theorem ClosedTermSubstitutionBoundarySelfCompileRoute [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                  UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                    Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                      Cont ledger audit route ∧ Cont route audit consumer ∧
                        PkgSig bundle consumer pkg ∧
                          SemanticNameCert
                            (fun row : BHist =>
                              ClosedTermSubstitutionBoundaryClassifier source value depth shift
                                substitution ∧ hsame row consumer)
                            (fun row : BHist =>
                              Cont route audit row ∧ PkgSig bundle consumer pkg)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle consumer pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
  have classifierWitness :
      ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution :=
    classifier
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
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
            hsame row consumer)
        (fun row : BHist => Cont route audit row ∧ PkgSig bundle consumer pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumer pkg)
        hsame :=
    ClosedTermSubstitutionBoundaryNamecertObligations classifierWitness shiftSubstitutionLedger
      substitutionDepthAudit ledgerAuditRoute routeAuditConsumer consumerPkg
  exact
    ⟨shiftUnary, substitutionUnary, ledgerUnary, auditUnary, routeUnary, consumerUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      consumerPkg, cert⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
