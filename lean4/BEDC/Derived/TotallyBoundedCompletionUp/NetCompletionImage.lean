import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_net_completion_image [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName finiteNetRead completionRead separatedRead imageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net finiteNetRead ->
        Cont embedding completion completionRead ->
          Cont completionRead separated separatedRead ->
            Cont separated extension imageRead ->
              PkgSig bundle imageRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row imageRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
                        hsame row completion ∨ hsame row separated ∨ hsame row extension ∨
                          hsame row imageRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont source net finiteNetRead ∧
                        Cont embedding completion completionRead ∧
                          Cont completionRead separated separatedRead ∧
                            Cont separated extension imageRead ∧
                              PkgSig bundle imageRead pkg)
                    hsame ∧
                  UnaryHistory finiteNetRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory separatedRead ∧ UnaryHistory imageRead := by
  -- BEDC touchpoint anchor: TotallyBoundedCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceNetFiniteRead embeddingCompletionRead completionSeparatedRead
    separatedExtensionImage imagePkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, _localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed sourceUnary netUnary sourceNetFiniteRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionRead
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed completionReadUnary separatedUnary completionSeparatedRead
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionImage
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row imageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row net ∨ hsame row refinement ∨ hsame row basis ∨ hsame row completion ∨
              hsame row separated ∨ hsame row extension ∨ hsame row imageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net finiteNetRead ∧
              Cont embedding completion completionRead ∧
                Cont completionRead separated separatedRead ∧
                  Cont separated extension imageRead ∧ PkgSig bundle imageRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro imageRead ⟨hsame_refl imageRead, imageUnary⟩
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
      exact
        ⟨source.right, sourceNetFiniteRead, embeddingCompletionRead, completionSeparatedRead,
          separatedExtensionImage, imagePkg⟩
  }
  exact ⟨cert, finiteNetUnary, completionReadUnary, separatedReadUnary, imageUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
