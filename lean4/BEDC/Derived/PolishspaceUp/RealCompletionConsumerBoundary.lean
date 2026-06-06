import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceRealCompletionConsumerBoundary [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName completionRead denseRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg ->
      Cont complete stream completionRead ->
        Cont separable stream denseRead ->
          Cont completionRead readback realRead ->
            PkgSig bundle localName pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                      hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                        hsame row realRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: PolishspaceRootCauchyBasisCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completeStreamCompletion separableStreamDense completionReadbackReal
    localNamePkg
  obtain ⟨_metricUnary, completeUnary, separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, _alignmentUnary, _transportUnary, _localNameUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, routeAndProvenance⟩ := carrier
  obtain ⟨_ledgerTransportRoute, provenancePkg⟩ := routeAndProvenance
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed completionUnary readbackUnary completionReadbackReal
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, realUnary⟩

end BEDC.Derived.PolishspaceUp
