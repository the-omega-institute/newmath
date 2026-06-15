import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_no_escape [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont transport provenance exportedRead →
        PkgSig bundle exportedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
                  hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                    hsame row extension ∨ hsame row transport ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row exportedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle exportedRead pkg ∧ PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory exportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier transportProvenanceExported exportedPackage
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    separatedExtensionProvenance, transportProvenanceLocalName, _provenancePackage,
    localPackage⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionProvenance
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceExported
  have sourceAtExported : hsame exportedRead exportedRead ∧ UnaryHistory exportedRead :=
    ⟨hsame_refl exportedRead, exportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row transport ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row exportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle exportedRead pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportedRead sourceAtExported
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
      exact ⟨source.right, exportedPackage, localPackage⟩
  }
  exact ⟨cert, exportedUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
