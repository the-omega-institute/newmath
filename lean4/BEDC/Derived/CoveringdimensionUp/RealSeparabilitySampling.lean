import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilitySampling [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName denseWindow sampledCover : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet denseWindow →
        Cont denseWindow cover sampledCover →
          PkgSig bundle sampledCover pkg →
            UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
              UnaryHistory denseWindow ∧ UnaryHistory sampledCover ∧
                Cont compactMetric epsilonNet denseWindow ∧
                  Cont denseWindow cover sampledCover ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sampledCover pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier denseRoute sampledRoute sampledPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have denseUnary : UnaryHistory denseWindow :=
    unary_cont_closed compactUnary epsilonUnary denseRoute
  have sampledUnary : UnaryHistory sampledCover :=
    unary_cont_closed denseUnary coverUnary sampledRoute
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, denseUnary, sampledUnary, denseRoute,
      sampledRoute, provenancePkg, sampledPkg⟩

end BEDC.Derived.CoveringdimensionUp
