import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNameCertThresholdPackage [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route ledger thresholdRead ->
              PkgSig bundle thresholdRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      ClosedTermSubstitutionBoundaryClassifier source value depth shift
                        substitution ∧ hsame row thresholdRead)
                    (fun row : BHist => Cont route ledger row ∧ PkgSig bundle thresholdRead pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle thresholdRead pkg)
                    hsame ∧
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory thresholdRead ∧ PkgSig bundle thresholdRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeLedgerThreshold thresholdPkg
  have classifierWitness := classifier
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed routeUnary ledgerUnary routeLedgerThreshold
  have sourceThreshold :
      (fun row : BHist =>
        ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
          hsame row thresholdRead) thresholdRead :=
    ⟨classifierWitness, hsame_refl thresholdRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
              hsame row thresholdRead)
          (fun row : BHist => Cont route ledger row ∧ PkgSig bundle thresholdRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle thresholdRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro thresholdRead sourceThreshold
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport routeLedgerThreshold (hsame_symm source.right),
          thresholdPkg⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport thresholdUnary (hsame_symm source.right), thresholdPkg⟩
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, thresholdUnary, thresholdPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
