import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRouteSaturation [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                  UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                    UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit consumer ∧
                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
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
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, shiftSubstitutionLedger,
      substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer, consumerPkg⟩

theorem ClosedTermSubstitutionBoundaryConsumerNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row value ∨ hsame row depth ∨
                        hsame row ledger ∨ hsame row audit ∨ hsame row route ∨
                          hsame row consumer)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont ledger audit route ∧
                        Cont route audit consumer ∧ PkgSig bundle consumer pkg)
                    hsame ∧
                  UnaryHistory consumer := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
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
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨ hsame row ledger ∨
              hsame row audit ∨ hsame row route ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger audit route ∧ Cont route audit consumer ∧
              PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerAuditRoute, routeAuditConsumer, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
