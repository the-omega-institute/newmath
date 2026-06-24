import BEDC.Derived.ArchimedeanOrderedFieldUp.Carrier

namespace BEDC.Derived.ArchimedeanOrderedFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanOrderedFieldScopedClosure [AskSetup] [PackageSetup]
    {real alg rat bound ledger transport route provenance localCert rootRead
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
        localCert bundle pkg →
      Cont localCert route rootRead →
        Cont ledger bound comparisonRead →
          PkgSig bundle rootRead pkg →
            PkgSig bundle comparisonRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row rootRead ∨ hsame row comparisonRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row real ∨ hsame row alg ∨ hsame row rat ∨ hsame row bound ∨
                      hsame row ledger ∨ hsame row route ∨ hsame row provenance ∨
                        hsame row localCert ∨ hsame row rootRead ∨
                          hsame row comparisonRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
                      Cont localCert route rootRead ∧ PkgSig bundle rootRead pkg ∧
                        PkgSig bundle comparisonRead pkg)
                  hsame ∧ UnaryHistory rootRead ∧ UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier rootRoute comparisonRoute rootPkg comparisonPkg
  obtain ⟨realUnary, algUnary, ratUnary, boundUnary, ledgerUnary, provenanceUnary,
    localCertUnary, realAlgLedger, ledgerBoundRoute, _routeProvenanceCert,
    _provenancePkg, _localCertPkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary boundUnary ledgerBoundRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed localCertUnary routeUnary rootRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed ledgerUnary boundUnary comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row rootRead ∨ hsame row comparisonRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row real ∨ hsame row alg ∨ hsame row rat ∨ hsame row bound ∨
              hsame row ledger ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localCert ∨ hsame row rootRead ∨ hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
              Cont localCert route rootRead ∧ PkgSig bundle rootRead pkg ∧
                PkgSig bundle comparisonRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead
        ⟨Or.inl (hsame_refl rootRead), rootUnary⟩
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
          ⟨by
            cases source.left with
            | inl sameRoot =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameRoot)
            | inr sameComparison =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameComparison),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRoot =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl sameRoot))))))))
      | inr sameComparison =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr sameComparison))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realAlgLedger, ledgerBoundRoute, rootRoute, rootPkg, comparisonPkg⟩
  }
  exact ⟨cert, rootUnary, comparisonUnary⟩

end BEDC.Derived.ArchimedeanOrderedFieldUp
