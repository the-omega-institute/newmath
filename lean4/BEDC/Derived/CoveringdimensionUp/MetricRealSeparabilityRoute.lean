import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionMetricRealSeparabilityRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead denseWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead lebesgue denseWindow →
          PkgSig bundle denseWindow pkg →
            SemanticNameCert
                (fun row : BHist => hsame row denseWindow ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                    hsame row lebesgue ∨ hsame row denseWindow)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                    Cont metricRead lebesgue denseWindow ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle denseWindow pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory denseWindow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute denseRoute densePkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have denseUnary : UnaryHistory denseWindow :=
    unary_cont_closed metricUnary lebesgueUnary denseRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denseWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row lebesgue ∨ hsame row denseWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead lebesgue denseWindow ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle denseWindow pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro denseWindow ⟨hsame_refl denseWindow, denseUnary⟩
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
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, metricRoute, denseRoute, provenancePkg, densePkg⟩
  }
  exact ⟨cert, metricUnary, denseUnary⟩

end BEDC.Derived.CoveringdimensionUp
