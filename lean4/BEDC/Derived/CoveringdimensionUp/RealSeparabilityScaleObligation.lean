import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityScaleObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName separabilityRead toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound separabilityRead →
        Cont separabilityRead lebesgue toleranceRead →
          PkgSig bundle toleranceRead pkg →
            UnaryHistory cover ∧ UnaryHistory orderBound ∧ UnaryHistory separabilityRead ∧
              UnaryHistory toleranceRead ∧ Cont compactMetric epsilonNet cover ∧
                Cont cover refinement orderBound ∧ Cont cover orderBound separabilityRead ∧
                  Cont separabilityRead lebesgue toleranceRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle toleranceRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverOrderSeparability separabilityLebesgueTolerance tolerancePkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have separabilityUnary : UnaryHistory separabilityRead :=
    unary_cont_closed coverUnary orderUnary coverOrderSeparability
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed separabilityUnary lebesgueUnary separabilityLebesgueTolerance
  exact
    ⟨coverUnary, orderUnary, separabilityUnary, toleranceUnary, compactEpsilonCover,
      coverRefinementOrder, coverOrderSeparability, separabilityLebesgueTolerance,
      provenancePkg, tolerancePkg⟩

end BEDC.Derived.CoveringdimensionUp
