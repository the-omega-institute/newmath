import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRefinementOrderRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinementRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement refinementRead →
        Cont refinementRead orderBound rootRead →
          PkgSig bundle rootRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory cover ∧ UnaryHistory refinement ∧
              UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧ UnaryHistory refinementRead ∧
                UnaryHistory rootRead ∧ Cont compactMetric epsilonNet cover ∧
                  Cont cover refinement orderBound ∧ Cont cover refinement refinementRead ∧
                    Cont refinementRead orderBound rootRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRefinementRead refinementReadOrderRoot rootReadPkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed refinementReadUnary orderUnary refinementReadOrderRoot
  exact
    ⟨compactUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      refinementReadUnary, rootReadUnary, compactEpsilonCover, coverRefinementOrder,
      coverRefinementRead, refinementReadOrderRoot, provenancePkg, rootReadPkg⟩

theorem CoveringDimensionCoverOrderDirectedness [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName leftRefinement rightRefinement commonRefinement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement leftRefinement →
        Cont cover refinement rightRefinement →
          Cont leftRefinement rightRefinement commonRefinement →
            PkgSig bundle commonRefinement pkg →
              UnaryHistory cover ∧ UnaryHistory refinement ∧ UnaryHistory leftRefinement ∧
                UnaryHistory rightRefinement ∧ UnaryHistory commonRefinement ∧
                  Cont cover refinement leftRefinement ∧
                    Cont cover refinement rightRefinement ∧
                      Cont leftRefinement rightRefinement commonRefinement ∧
                        PkgSig bundle commonRefinement pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRefinementLeft coverRefinementRight leftRightCommon commonPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have leftUnary : UnaryHistory leftRefinement :=
    unary_cont_closed coverUnary refinementUnary coverRefinementLeft
  have rightUnary : UnaryHistory rightRefinement :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRight
  have commonUnary : UnaryHistory commonRefinement :=
    unary_cont_closed leftUnary rightUnary leftRightCommon
  exact
    ⟨coverUnary, refinementUnary, leftUnary, rightUnary, commonUnary, coverRefinementLeft,
      coverRefinementRight, leftRightCommon, commonPkg⟩

theorem CoveringDimensionCarrier_root_separability_route [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName separabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound separabilityRead →
        PkgSig bundle separabilityRead pkg →
          UnaryHistory cover ∧ UnaryHistory orderBound ∧ UnaryHistory separabilityRead ∧
            Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
              Cont cover orderBound separabilityRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle separabilityRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverOrderSeparability separabilityPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have separabilityUnary : UnaryHistory separabilityRead :=
    unary_cont_closed coverUnary orderUnary coverOrderSeparability
  exact
    ⟨coverUnary, orderUnary, separabilityUnary, compactEpsilonCover, coverRefinementOrder,
      coverOrderSeparability, provenancePkg, separabilityPkg⟩

theorem CoveringDimensionCarrier_root_completion_handoff [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont lebesgue replay completionRead →
        PkgSig bundle completionRead pkg →
          UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
            UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
              UnaryHistory completionRead ∧ Cont compactMetric epsilonNet cover ∧
                Cont cover refinement orderBound ∧ Cont orderBound lebesgue replay ∧
                  Cont lebesgue replay completionRead ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lebesgueReplayCompletion completionPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, compactEpsilonCover,
    coverRefinementOrder, orderLebesgueReplay, _transportReplayProvenance, _provenancePkg,
    _localNamePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed lebesgueUnary replayUnary lebesgueReplayCompletion
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      completionUnary, compactEpsilonCover, coverRefinementOrder, orderLebesgueReplay,
      lebesgueReplayCompletion, completionPkg⟩

end BEDC.Derived.CoveringdimensionUp
