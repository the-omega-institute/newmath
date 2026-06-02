import BEDC.Derived.PolishspaceUp.RootUnblockSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteMetricSourceLock [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      Cont metric complete completionRead →
        Cont metric separable denseRead →
          Cont completionRead denseRead sharedRead →
            SemanticNameCert
                (fun row : BHist => hsame row sharedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                    hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                      hsame row sharedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                UnaryHistory sharedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface metricComplete metricSeparable completionDense
  obtain ⟨metricUnary, completeUnary, separableUnary, _streamUnary, _readbackUnary,
    _ledgerUnary, _transportUnary, _metricCompleteRoot, _metricSeparableRoot,
    _ledgerTransportReplay, provenancePkg, localNamePkg⟩ := surface
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricComplete
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparable
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed completionUnary denseUnary completionDense
  have sourceShared :
      (fun row : BHist => hsame row sharedRead ∧ UnaryHistory row) sharedRead := by
    exact ⟨hsame_refl sharedRead, sharedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sharedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row sharedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sharedRead sourceShared
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
  exact ⟨cert, completionUnary, denseUnary, sharedUnary⟩

end BEDC.Derived.PolishspaceUp
