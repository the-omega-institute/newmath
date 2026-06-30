import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_scoped_consumer_coverage [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName completionRead extensionRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont refinement basis completionRead ->
        Cont separated extension extensionRead ->
          Cont completionRead extensionRead scopedRead ->
            PkgSig bundle scopedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                      hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                        hsame row separated ∨ hsame row extension ∨ hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle scopedRead pkg ∧
                      PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier completionRoute extensionRoute scopedRoute scopedPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, separatedExtensionProvenance, _transportProvenanceLocalName,
    provenancePkg, _localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed refinementUnary basisUnary completionRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedUnary extensionUnary extensionRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed completionReadUnary extensionReadUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle scopedRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact ⟨source.right, scopedPkg, provenancePkg⟩
  }
  exact ⟨cert, scopedUnary⟩

theorem TotallyBoundedCompletionCarrier_scope_dependency_seal [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName extensionRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont extension transport extensionRead ->
        Cont extensionRead localName scopedRead ->
          PkgSig bundle scopedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                    hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                      hsame row separated ∨ hsame row extension ∨ hsame row transport ∨
                        hsame row localName ∨ hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont source net refinement ∧
                    Cont refinement basis embedding ∧ Cont embedding completion separated ∧
                      Cont separated extension provenance ∧ Cont transport provenance localName ∧
                        Cont extension transport extensionRead ∧
                          Cont extensionRead localName scopedRead ∧
                            PkgSig bundle scopedRead pkg)
                hsame ∧ UnaryHistory scopedRead ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier extensionTransportRead scopedRoute scopedPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    separatedExtensionProvenance, transportProvenanceLocalName, _provenancePkg,
    localNamePkg⟩ := carrier
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
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed extensionUnary transportUnary extensionTransportRead
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed extensionReadUnary localNameUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row transport ∨ hsame row localName ∨
                  hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net refinement ∧ Cont refinement basis embedding ∧
              Cont embedding completion separated ∧ Cont separated extension provenance ∧
                Cont transport provenance localName ∧ Cont extension transport extensionRead ∧
                  Cont extensionRead localName scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceNetRefinement, refinementBasisEmbedding,
          embeddingCompletionSeparated, separatedExtensionProvenance, transportProvenanceLocalName,
          extensionTransportRead, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary, localNamePkg, scopedPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
