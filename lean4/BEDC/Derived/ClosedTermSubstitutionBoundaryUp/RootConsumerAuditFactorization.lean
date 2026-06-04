import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootConsumerAuditFactorization [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route rootRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit rootRead ->
              Cont audit rootRead auditRead ->
                PkgSig bundle auditRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row value ∨ hsame row depth ∨
                          hsame row ledger ∨ hsame row audit ∨ hsame row route ∨
                            hsame row rootRead ∨ hsame row auditRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont ledger audit route ∧
                          Cont route audit rootRead ∧ Cont audit rootRead auditRead ∧
                            PkgSig bundle auditRead pkg)
                      hsame ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory rootRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRoot auditRootAuditRead auditReadPkg
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
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary rootUnary auditRootAuditRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨
              hsame row ledger ∨ hsame row audit ∨ hsame row route ∨
                hsame row rootRead ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger audit route ∧ Cont route audit rootRead ∧
              Cont audit rootRead auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditReadUnary⟩
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
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerAuditRoute, routeAuditRoot, auditRootAuditRead, auditReadPkg⟩
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, rootUnary, auditReadUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
