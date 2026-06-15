import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_net_filter_carrier_admission
    [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont net refinement netRead →
        PkgSig bundle netRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row net ∨ hsame row refinement ∨ hsame row netRead ∨
                    hsame row localName) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                  hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                    hsame row netRead ∨ hsame row localName)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont source net refinement ∧ Cont net refinement netRead ∧
                  PkgSig bundle netRead pkg)
              hsame ∧
            UnaryHistory netRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier netRefinementRead netReadPkg
  obtain
    ⟨sourceUnary, netUnary, refinementUnary, basisUnary, embeddingUnary, completionUnary,
      _separatedUnary, _extensionUnary, _transportUnary, _provenanceUnary, localNameUnary,
      localNamePkg⟩ :=
    TotallyBoundedCompletionCarrier_namecert_obligations (pkg := pkg) carrier
  obtain ⟨_sourceUnary0, _netUnary0, _basisUnary0, _completionUnary0, _extensionUnary0,
    _transportUnary0, sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, _localNamePkg0⟩ := carrier
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed netUnary refinementUnary netRefinementRead
  have sourceAtNetRead :
      (hsame netRead net ∨ hsame netRead refinement ∨ hsame netRead netRead ∨
            hsame netRead localName) ∧
        UnaryHistory netRead :=
    ⟨Or.inr (Or.inr (Or.inl (hsame_refl netRead))), netReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row net ∨ hsame row refinement ∨ hsame row netRead ∨
                hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row netRead ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net refinement ∧ Cont net refinement netRead ∧
              PkgSig bundle netRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro netRead sourceAtNetRead
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
        cases source with
        | intro displayed rowUnary =>
            have otherUnary : UnaryHistory _other :=
              unary_transport rowUnary sameRows
            have otherDisplayed :
                hsame _other net ∨ hsame _other refinement ∨ hsame _other netRead ∨
                  hsame _other localName := by
              cases displayed with
              | inl sameNet =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameNet)
              | inr rest =>
                  cases rest with
                  | inl sameRefinement =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRefinement))
                  | inr rest2 =>
                      cases rest2 with
                      | inl sameNetRead =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameNetRead)))
                      | inr sameLocalName =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr (hsame_trans (hsame_symm sameRows) sameLocalName)))
            exact ⟨otherDisplayed, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameNet =>
          exact Or.inr (Or.inl sameNet)
      | inr rest =>
          cases rest with
          | inl sameRefinement =>
              exact Or.inr (Or.inr (Or.inl sameRefinement))
          | inr rest2 =>
              cases rest2 with
              | inl sameNetRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameNetRead))))))
              | inr sameLocalName =>
                  cases sameLocalName
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (hsame_refl localName)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceNetRefinement, netRefinementRead, netReadPkg⟩
  }
  exact ⟨cert, netReadUnary, localNamePkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
