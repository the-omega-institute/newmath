import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_uniform_extension_ledger [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont separated extension extensionRead ->
        PkgSig bundle extensionRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
                  hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                    hsame row extensionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle extensionRead pkg)
              hsame ∧
            UnaryHistory extensionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier separatedExtensionRead extensionReadPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, _transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    _separatedExtensionProvenance, _transportProvenanceLocalName, _provenancePkg,
    localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionRead
  have sourceAtExtension :
      (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row) extensionRead := by
    exact ⟨hsame_refl extensionRead, extensionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle extensionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro extensionRead sourceAtExtension
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, extensionReadPkg⟩
  }
  exact ⟨cert, extensionReadUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
