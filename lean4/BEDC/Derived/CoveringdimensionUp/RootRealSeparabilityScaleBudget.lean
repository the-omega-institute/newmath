import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRealSeparabilityScaleBudget [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityRead nerveRead scaleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet densityRead →
        Cont densityRead cover nerveRead →
          Cont nerveRead lebesgue scaleRead →
            PkgSig bundle scaleRead pkg →
              UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
                UnaryHistory lebesgue ∧ UnaryHistory densityRead ∧
                  UnaryHistory nerveRead ∧ UnaryHistory scaleRead ∧
                    Cont compactMetric epsilonNet densityRead ∧
                      Cont densityRead cover nerveRead ∧
                        Cont nerveRead lebesgue scaleRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle scaleRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier densityRoute nerveRoute scaleRoute scalePkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed compactUnary epsilonUnary densityRoute
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary coverUnary nerveRoute
  have scaleUnary : UnaryHistory scaleRead :=
    unary_cont_closed nerveUnary lebesgueUnary scaleRoute
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, lebesgueUnary, densityUnary, nerveUnary,
      scaleUnary, densityRoute, nerveRoute, scaleRoute, provenancePkg, scalePkg⟩

end BEDC.Derived.CoveringdimensionUp
