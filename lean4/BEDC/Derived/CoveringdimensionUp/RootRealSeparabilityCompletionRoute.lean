import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRealSeparabilityCompletionRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName realWindow completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont lebesgue replay realWindow →
        Cont realWindow localName completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory cover ∧ UnaryHistory lebesgue ∧
              UnaryHistory replay ∧ UnaryHistory localName ∧ UnaryHistory realWindow ∧
                UnaryHistory completionRead ∧ Cont compactMetric epsilonNet cover ∧
                  Cont orderBound lebesgue replay ∧ Cont lebesgue replay realWindow ∧
                    Cont realWindow localName completionRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lebesgueReplayRealWindow realWindowLocalNameCompletion completionPkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    compactEpsilonCover, _coverRefinementOrder, orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed lebesgueUnary replayUnary lebesgueReplayRealWindow
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realWindowUnary localNameUnary realWindowLocalNameCompletion
  exact
    ⟨compactUnary, coverUnary, lebesgueUnary, replayUnary, localNameUnary, realWindowUnary,
      completionReadUnary, compactEpsilonCover, orderLebesgueReplay, lebesgueReplayRealWindow,
      realWindowLocalNameCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.CoveringdimensionUp
