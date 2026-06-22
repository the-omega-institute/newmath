import BEDC.Derived.ArchimedeanOrderedFieldUp.Carrier

namespace BEDC.Derived.ArchimedeanOrderedFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanOrderedFieldRootObligationPackage [AskSetup] [PackageSetup]
    {real alg rat bound ledger transport route provenance localCert rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
        localCert bundle pkg →
      Cont localCert route rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row real ∨ hsame row alg ∨ hsame row rat ∨ hsame row bound ∨
                  hsame row ledger ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row localCert ∨ hsame row rootRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
                  Cont route provenance localCert ∧ Cont localCert route rootRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
              hsame ∧
            UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier rootRoute rootPkg
  obtain
    ⟨realUnary, algUnary, _ratUnary, boundUnary, ledgerUnary, provenanceUnary,
      localCertUnary, realAlgLedger, ledgerBoundRoute, routeProvenanceCert,
      provenancePkg, _localCertPkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary boundUnary ledgerBoundRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed localCertUnary routeUnary rootRoute
  have sourceRoot :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row real ∨ hsame row alg ∨ hsame row rat ∨ hsame row bound ∨
              hsame row ledger ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localCert ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
              Cont route provenance localCert ∧ Cont localCert route rootRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRoot
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
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, realAlgLedger, ledgerBoundRoute, routeProvenanceCert,
          rootRoute, provenancePkg, rootPkg⟩
  }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.ArchimedeanOrderedFieldUp
