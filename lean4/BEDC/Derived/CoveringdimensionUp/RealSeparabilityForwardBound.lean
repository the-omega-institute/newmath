import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityForwardBound [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover densityRead →
        Cont densityRead orderBound boundRead →
          PkgSig bundle boundRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
              UnaryHistory orderBound ∧ UnaryHistory densityRead ∧ UnaryHistory boundRead ∧
                Cont compactMetric epsilonNet cover ∧ Cont epsilonNet cover densityRead ∧
                  Cont densityRead orderBound boundRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle boundRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier epsilonCoverDensity densityOrderBound boundPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverDensity
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed densityUnary orderUnary densityOrderBound
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, orderUnary, densityUnary, boundUnary,
      compactEpsilonCover, epsilonCoverDensity, densityOrderBound, provenancePkg, boundPkg⟩

end BEDC.Derived.CoveringdimensionUp
