import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionPublicFiniteNetRoute [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName finiteNetRead completionRead extensionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net finiteNetRead ->
        Cont embedding completion completionRead ->
          Cont separated extension extensionRead ->
            Cont completionRead extensionRead publicRead ->
              PkgSig bundle finiteNetRead pkg ->
                PkgSig bundle completionRead pkg ->
                  PkgSig bundle extensionRead pkg ->
                    PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                              hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                                hsame row separated ∨ hsame row extension ∨
                                  hsame row finiteNetRead ∨ hsame row completionRead ∨
                                    hsame row extensionRead ∨ hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont source net finiteNetRead ∧
                              Cont embedding completion completionRead ∧
                                Cont separated extension extensionRead ∧
                                  Cont completionRead extensionRead publicRead ∧
                                    PkgSig bundle publicRead pkg)
                          hsame ∧ UnaryHistory finiteNetRead ∧ UnaryHistory completionRead ∧
                        UnaryHistory extensionRead ∧ UnaryHistory publicRead ∧
                          PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier finiteNetRoute completionRoute extensionRoute publicRoute finiteNetPkg
    completionPkg extensionPkg publicPkg
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
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed sourceUnary netUnary finiteNetRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingUnary completionUnary completionRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedUnary extensionUnary extensionRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed completionReadUnary extensionReadUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row finiteNetRead ∨ hsame row completionRead ∨
                  hsame row extensionRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net finiteNetRead ∧
              Cont embedding completion completionRead ∧ Cont separated extension extensionRead ∧
                Cont completionRead extensionRead publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
                        (Or.inr
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, finiteNetRoute, completionRoute, extensionRoute, publicRoute, publicPkg⟩
  }
  exact
    ⟨cert, finiteNetUnary, completionReadUnary, extensionReadUnary, publicReadUnary,
      localNamePkg⟩

theorem TotallyBoundedCompletionCarrier_public_finite_net_route [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName finiteNetRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net finiteNetRead ->
        Cont finiteNetRead localName publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                    hsame row finiteNetRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont source net finiteNetRead ∧
                    PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory finiteNetRead ∧ UnaryHistory publicRead ∧
                PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: TotallyBoundedCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier finiteNetRoute publicRoute publicPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary,
    transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, separatedExtensionProvenance,
    transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
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
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed sourceUnary netUnary finiteNetRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed finiteNetUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨
              hsame row finiteNetRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net finiteNetRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, finiteNetRoute, publicPkg⟩
  }
  exact ⟨cert, finiteNetUnary, publicUnary, localNamePkg⟩

theorem TotallyBoundedCompletionPublicFiniteNetRoute [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName completionRead extensionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont refinement basis completionRead -> Cont separated extension extensionRead ->
        Cont completionRead extensionRead publicRead -> PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                  hsame row separated ∨ hsame row extension ∨ hsame row transport ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont refinement basis completionRead ∧
                Cont separated extension extensionRead ∧
                  Cont completionRead extensionRead publicRead ∧
                    PkgSig bundle publicRead pkg)
            hsame ∧ UnaryHistory completionRead ∧ UnaryHistory extensionRead ∧
              UnaryHistory publicRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: TotallyBoundedCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute extensionRoute publicRoute publicPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, _transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    separatedExtensionProvenance, _transportProvenanceLocalName, provenancePkg,
    _localNamePkg⟩ := carrier
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
  have _provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionProvenance
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionReadUnary extensionReadUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row transport ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont refinement basis completionRead ∧
              Cont separated extension extensionRead ∧
                Cont completionRead extensionRead publicRead ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionRoute, extensionRoute, publicRoute, publicPkg⟩
  }
  exact
    ⟨cert, completionReadUnary, extensionReadUnary, publicUnary, provenancePkg, publicPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
