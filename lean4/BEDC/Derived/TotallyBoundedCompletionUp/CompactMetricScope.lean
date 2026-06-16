import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_compact_metric_scope [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont extension transport compactRead ->
        PkgSig bundle compactRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
                  hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                    hsame row extension ∨ hsame row compactRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle compactRead pkg ∧
                  PkgSig bundle localName pkg)
              hsame ∧ UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: TotallyBoundedCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute compactPkg
  obtain ⟨_sourceUnary, _netUnary, _basisUnary, _completionUnary, extensionUnary,
    transportUnary, _sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed extensionUnary transportUnary compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row net ∨ hsame row refinement ∨ hsame row basis ∨ hsame row embedding ∨
              hsame row completion ∨ hsame row separated ∨ hsame row extension ∨
                hsame row compactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle compactRead pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactPkg, localNamePkg⟩
  }
  exact ⟨cert, compactUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
