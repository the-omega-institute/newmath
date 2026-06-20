import BEDC.Derived.ClaimStatusAuditUp

namespace BEDC.Derived.ClaimStatusAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClaimStatusAuditCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {expression theoremRow route evidence gap socket admission exportRow transport replay provenance
      localName routeRead statusRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClaimStatusAuditCarrier expression theoremRow route evidence gap socket admission exportRow
        transport replay provenance localName bundle pkg ->
      Cont expression theoremRow routeRead ->
        Cont routeRead evidence statusRead ->
          Cont statusRead exportRow publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row expression ∨ hsame row theoremRow ∨ hsame row route ∨
                      hsame row evidence ∨ hsame row gap ∨ hsame row socket ∨
                        hsame row admission ∨ hsame row exportRow ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont expression theoremRow routeRead ∧
                      Cont routeRead evidence statusRead ∧ Cont statusRead exportRow publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory routeRead ∧ UnaryHistory statusRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier expressionTheorem routeEvidence statusExport publicPkg
  obtain ⟨expressionUnary, theoremUnary, _routeUnary, evidenceUnary, _gapUnary, _socketUnary,
    _admissionUnary, exportRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed expressionUnary theoremUnary expressionTheorem
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed routeReadUnary evidenceUnary routeEvidence
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed statusReadUnary exportRowUnary statusExport
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row expression ∨ hsame row theoremRow ∨ hsame row route ∨
              hsame row evidence ∨ hsame row gap ∨ hsame row socket ∨
                hsame row admission ∨ hsame row exportRow ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont expression theoremRow routeRead ∧
              Cont routeRead evidence statusRead ∧ Cont statusRead exportRow publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, expressionTheorem, routeEvidence, statusExport, publicPkg⟩
  }
  exact ⟨cert, routeReadUnary, statusReadUnary, publicReadUnary⟩

end BEDC.Derived.ClaimStatusAuditUp
