import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootMetricRealWindowSeparation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead realWindow nerveRead dimensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric cover metricRead →
        Cont metricRead lebesgue realWindow →
          Cont realWindow orderBound nerveRead →
            Cont nerveRead localName dimensionRead →
              PkgSig bundle dimensionRead pkg →
                UnaryHistory metricRead ∧ UnaryHistory realWindow ∧
                  UnaryHistory nerveRead ∧ UnaryHistory dimensionRead ∧
                    Cont compactMetric cover metricRead ∧
                      Cont metricRead lebesgue realWindow ∧
                        Cont realWindow orderBound nerveRead ∧
                          Cont nerveRead localName dimensionRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle dimensionRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier compactCoverMetric metricLebesgueReal realOrderNerve nerveLocalDimension
    dimensionPkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary coverUnary compactCoverMetric
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed metricReadUnary lebesgueUnary metricLebesgueReal
  have nerveReadUnary : UnaryHistory nerveRead :=
    unary_cont_closed realWindowUnary orderUnary realOrderNerve
  have dimensionReadUnary : UnaryHistory dimensionRead :=
    unary_cont_closed nerveReadUnary localNameUnary nerveLocalDimension
  exact
    ⟨metricReadUnary, realWindowUnary, nerveReadUnary, dimensionReadUnary,
      compactCoverMetric, metricLebesgueReal, realOrderNerve, nerveLocalDimension,
      provenancePkg, dimensionPkg⟩

end BEDC.Derived.CoveringdimensionUp
