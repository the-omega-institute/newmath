import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRealSeparabilityWindowObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityRead refinementRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover densityRead →
        Cont densityRead refinement refinementRead →
          Cont refinementRead localName namedRead →
            PkgSig bundle namedRead pkg →
              UnaryHistory densityRead ∧ UnaryHistory refinementRead ∧
                UnaryHistory namedRead ∧ Cont compactMetric epsilonNet cover ∧
                  Cont epsilonNet cover densityRead ∧
                    Cont densityRead refinement refinementRead ∧
                      Cont refinementRead localName namedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier densityRoute refinementRoute namedRoute namedPkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityReadUnary : UnaryHistory densityRead :=
    unary_cont_closed epsilonUnary coverUnary densityRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed densityReadUnary refinementUnary refinementRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed refinementReadUnary localNameUnary namedRoute
  exact
    ⟨densityReadUnary, refinementReadUnary, namedReadUnary, compactEpsilonCover,
      densityRoute, refinementRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.CoveringdimensionUp
