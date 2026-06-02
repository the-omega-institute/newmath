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

theorem PolishSpaceMetricReadbackStability [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      metricReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg ->
      Cont metric complete metricReadback ->
        Cont metricReadback stream readback ->
          PkgSig bundle localName pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row metricReadback ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                    hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                      hsame row metricReadback)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ Cont metric complete metricReadback)
                hsame ∧
              UnaryHistory metricReadback ∧ UnaryHistory readback ∧
                UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro surface metricCompleteReadback readbackStreamReplay localNamePkg
  obtain ⟨metricUnary, completeUnary, _separableUnary, streamUnary, _readbackUnary,
    ledgerUnary, transportUnary, _metricCompleteAppend, _metricSeparableAppend,
    ledgerTransportReplay, provenancePkg, _surfaceLocalNamePkg⟩ := surface
  have metricReadbackUnary : UnaryHistory metricReadback :=
    unary_cont_closed metricUnary completeUnary metricCompleteReadback
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed metricReadbackUnary streamUnary readbackStreamReplay
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have sourceMetricReadback :
      (fun row : BHist => hsame row metricReadback ∧ UnaryHistory row)
        metricReadback := by
    exact ⟨hsame_refl metricReadback, metricReadbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricReadback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row metricReadback)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ Cont metric complete metricReadback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro metricReadback sourceMetricReadback
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
      exact ⟨source.right, provenancePkg, localNamePkg, metricCompleteReadback⟩
  }
  exact ⟨cert, metricReadbackUnary, readbackUnary, replayUnary⟩

end BEDC.Derived.PolishspaceUp
