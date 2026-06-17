import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_obligation_closure_route [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName finiteNetRead completionRead extensionRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont source net finiteNetRead →
        Cont embedding completion completionRead →
          Cont separated extension extensionRead →
            Cont finiteNetRead completionRead closureRead →
              PkgSig bundle closureRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                        hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                          hsame row separated ∨ hsame row extension ∨ hsame row closureRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont finiteNetRead completionRead closureRead ∧
                        PkgSig bundle closureRead pkg)
                    hsame ∧
                  UnaryHistory finiteNetRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory extensionRead ∧ UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier finiteNetRoute completionRoute extensionRoute closureRoute closurePkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, _transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    _separatedExtensionProvenance, _transportProvenanceLocalName, _provenancePkg,
    _localNamePkg⟩ := carrier
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
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed finiteNetUnary completionReadUnary closureRoute
  have sourceAtClosure : hsame closureRead closureRead ∧ UnaryHistory closureRead :=
    ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont finiteNetRead completionRead closureRead ∧
              PkgSig bundle closureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead sourceAtClosure
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
      intro row source
      exact ⟨source.right, closureRoute, closurePkg⟩
  }
  exact ⟨cert, finiteNetUnary, completionReadUnary, extensionReadUnary, closureUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
