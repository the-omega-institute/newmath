import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_root_route_exhaustion [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName completionRead extensionRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont embedding completion completionRead ->
        Cont extension transport extensionRead ->
          Cont extensionRead localName consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row net ∨ hsame row basis ∨
                      hsame row completionRead ∨ hsame row consumerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont source net refinement ∧
                      Cont refinement basis embedding ∧
                        Cont embedding completion completionRead ∧
                          PkgSig bundle consumerRead pkg)
                  hsame ∧
                UnaryHistory completionRead ∧ UnaryHistory extensionRead ∧
                  UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier completionRoute extensionRoute consumerRoute consumerPackage
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    separatedExtensionProvenance, transportProvenanceLocalName, _provenancePackage,
    _localPackage⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionProvenance
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceLocalName
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingUnary completionUnary completionRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed extensionUnary transportUnary extensionRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed extensionReadUnary localNameUnary consumerRoute
  have consumerSource :
      hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row basis ∨
              hsame row completionRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net refinement ∧ Cont refinement basis embedding ∧
              Cont embedding completion completionRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead consumerSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceNetRefinement, refinementBasisEmbedding, completionRoute,
          consumerPackage⟩
  }
  exact ⟨cert, completionReadUnary, extensionReadUnary, consumerReadUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
