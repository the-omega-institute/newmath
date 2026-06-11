import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverScopeGrounding [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead realRead denseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg ->
      Cont compactMetric epsilonNet metricRead ->
        Cont metricRead lebesgue realRead ->
          Cont realRead replay denseRead ->
            PkgSig bundle denseRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                      hsame row lebesgue ∨ hsame row realRead ∨ hsame row denseRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                      Cont metricRead lebesgue realRead ∧ Cont realRead replay denseRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle denseRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory realRead ∧ UnaryHistory denseRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactEpsilonMetric metricLebesgueReal realReplayDense densePkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary compactEpsilonMetric
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed metricUnary lebesgueUnary metricLebesgueReal
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed realUnary replayUnary realReplayDense
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro denseRead ⟨hsame_refl denseRead, denseUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, compactEpsilonMetric, metricLebesgueReal, realReplayDense,
            provenancePkg, densePkg⟩
    }
  · exact ⟨metricUnary, realUnary, denseUnary⟩

end BEDC.Derived.CoveringdimensionUp
