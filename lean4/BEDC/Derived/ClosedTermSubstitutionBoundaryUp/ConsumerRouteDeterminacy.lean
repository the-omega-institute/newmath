import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryConsumerRouteDeterminacy [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              hsame consumer consumer' ->
                PkgSig bundle consumer' pkg ->
                  UnaryHistory consumer' ∧ PkgSig bundle consumer' pkg ∧
                    SemanticNameCert
                      (fun row : BHist =>
                        ClosedTermSubstitutionBoundaryClassifier source value depth shift
                          substitution ∧ hsame row consumer')
                      (fun row : BHist =>
                        Cont route audit row ∧ PkgSig bundle consumer' pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumer' pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer sameConsumer consumerPkg
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
  have consumerUnary' : UnaryHistory consumer' :=
    unary_transport consumerUnary sameConsumer
  have routeAuditConsumer' : Cont route audit consumer' :=
    cont_result_hsame_transport routeAuditConsumer sameConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
              hsame row consumer')
          (fun row : BHist => Cont route audit row ∧ PkgSig bundle consumer' pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumer' pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer' ⟨classifierWitness, hsame_refl consumer'⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport routeAuditConsumer' (hsame_symm source.right),
          consumerPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport consumerUnary' (hsame_symm source.right), consumerPkg⟩
  }
  exact ⟨consumerUnary', consumerPkg, cert⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
