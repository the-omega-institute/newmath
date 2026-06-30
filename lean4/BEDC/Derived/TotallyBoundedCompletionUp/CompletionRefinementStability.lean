import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionRefinementStability [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName refinementRead completionRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont net refinement refinementRead →
        Cont refinementRead basis completionRead →
          Cont completionRead extension stableRead →
            PkgSig bundle stableRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
                      hsame row completionRead ∨ hsame row extension ∨ hsame row stableRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont net refinement refinementRead ∧
                      Cont refinementRead basis completionRead ∧
                        Cont completionRead extension stableRead ∧
                          PkgSig bundle stableRead pkg)
                  hsame ∧
                UnaryHistory refinementRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier refinementRoute completionRoute stableRoute stablePkg
  obtain ⟨sourceUnary, netUnary, basisUnary, _completionUnary, extensionUnary,
    _transportUnary, sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, _localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed netUnary refinementUnary refinementRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed refinementReadUnary basisUnary completionRoute
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed completionReadUnary extensionUnary stableRoute
  have sourceStable :
      (fun row : BHist => hsame row stableRead ∧ UnaryHistory row) stableRead := by
    exact ⟨hsame_refl stableRead, stableReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row completionRead ∨ hsame row extension ∨ hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont net refinement refinementRead ∧
              Cont refinementRead basis completionRead ∧
                Cont completionRead extension stableRead ∧ PkgSig bundle stableRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro stableRead sourceStable
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, refinementRoute, completionRoute, stableRoute, stablePkg⟩
    }
  exact ⟨cert, refinementReadUnary, completionReadUnary, stableReadUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
