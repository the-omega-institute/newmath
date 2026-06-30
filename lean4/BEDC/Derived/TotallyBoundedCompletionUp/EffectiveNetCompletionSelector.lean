import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_effective_net_completion_selector [AskSetup]
    [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName selectorRead completionRead separatedRead extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont net refinement selectorRead ->
        Cont embedding completion completionRead ->
          Cont separated extension separatedRead ->
            Cont separatedRead transport extensionRead ->
              PkgSig bundle extensionRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row net ∨ hsame row refinement ∨ hsame row selectorRead ∨
                        hsame row completionRead ∨ hsame row separatedRead ∨
                          hsame row extensionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont net refinement selectorRead ∧
                        Cont embedding completion completionRead ∧
                          Cont separated extension separatedRead ∧
                            Cont separatedRead transport extensionRead ∧
                              PkgSig bundle extensionRead pkg)
                    hsame ∧
                  UnaryHistory selectorRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory separatedRead ∧ UnaryHistory extensionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier selectorRoute completionRoute separatedRoute extensionRoute extensionPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary,
    transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, _localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed netUnary refinementUnary selectorRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingUnary completionUnary completionRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed separatedUnary extensionUnary separatedRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedReadUnary transportUnary extensionRoute
  have sourceAtExtension : hsame extensionRead extensionRead ∧ UnaryHistory extensionRead :=
    ⟨hsame_refl extensionRead, extensionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row net ∨ hsame row refinement ∨ hsame row selectorRead ∨
              hsame row completionRead ∨ hsame row separatedRead ∨
                hsame row extensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont net refinement selectorRead ∧
              Cont embedding completion completionRead ∧
                Cont separated extension separatedRead ∧
                  Cont separatedRead transport extensionRead ∧
                    PkgSig bundle extensionRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectorRoute, completionRoute, separatedRoute, extensionRoute,
          extensionPkg⟩
  }
  exact ⟨cert, selectorUnary, completionReadUnary, separatedReadUnary, extensionReadUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
