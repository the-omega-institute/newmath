import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNamecertExportTotality [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer ledger exportRead ->
                PkgSig bundle exportRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        ClosedTermSubstitutionBoundaryClassifier source value depth shift
                          substitution ∧ hsame row exportRead)
                      (fun row : BHist =>
                        Cont consumer ledger row ∧ Cont shift substitution ledger ∧
                          Cont substitution depth audit ∧ PkgSig bundle exportRead pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle exportRead pkg)
                      hsame ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory consumer ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerLedgerExport exportPkg
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
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed consumerUnary ledgerUnary consumerLedgerExport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
              hsame row exportRead)
          (fun row : BHist =>
            Cont consumer ledger row ∧ Cont shift substitution ledger ∧
              Cont substitution depth audit ∧ PkgSig bundle exportRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead (And.intro classifierWitness (hsame_refl exportRead))
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
        intro _row _row' sameRows sourceData
        exact And.intro sourceData.left
          (hsame_trans (hsame_symm sameRows) sourceData.right)
    }
    pattern_sound := by
      intro _row sourceData
      exact
        ⟨cont_result_hsame_transport consumerLedgerExport (hsame_symm sourceData.right),
          shiftSubstitutionLedger, substitutionDepthAudit, exportPkg⟩
    ledger_sound := by
      intro _row sourceData
      exact And.intro (unary_transport exportUnary (hsame_symm sourceData.right)) exportPkg
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, consumerUnary, exportUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
