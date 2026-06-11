import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootConsumerNamecertSeparation [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route rootRead namecertRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit rootRead ->
              Cont rootRead ledger namecertRead ->
                PkgSig bundle namecertRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namecertRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row route ∨ hsame row rootRead ∨ hsame row namecertRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont ledger audit route ∧
                          Cont route audit rootRead ∧ Cont rootRead ledger namecertRead ∧
                            PkgSig bundle namecertRead pkg)
                      hsame ∧
                    UnaryHistory namecertRead := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRoot rootLedgerNamecert namecertPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  have namecertUnary : UnaryHistory namecertRead :=
    unary_cont_closed rootUnary ledgerUnary rootLedgerNamecert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namecertRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row rootRead ∨ hsame row namecertRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger audit route ∧ Cont route audit rootRead ∧
              Cont rootRead ledger namecertRead ∧ PkgSig bundle namecertRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namecertRead ⟨hsame_refl namecertRead, namecertUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact Or.inr (Or.inr sourceData.left)
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, ledgerAuditRoute, routeAuditRoot, rootLedgerNamecert,
          namecertPkg⟩
  }
  exact ⟨cert, namecertUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
