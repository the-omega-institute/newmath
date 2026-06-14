import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverScopedDependency [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound rootRead →
        Cont rootRead replay exportRead →
          PkgSig bundle exportRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
              UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
                UnaryHistory replay ∧ UnaryHistory rootRead ∧ UnaryHistory exportRead ∧
                  Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
                    Cont cover orderBound rootRead ∧ Cont rootRead replay exportRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier coverOrderRoot rootReplayExport exportPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary orderUnary coverOrderRoot
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed rootUnary replayUnary rootReplayExport
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      replayUnary, rootUnary, exportUnary, compactEpsilonCover, coverRefinementOrder,
      coverOrderRoot, rootReplayExport, provenancePkg, exportPkg⟩

end BEDC.Derived.CoveringdimensionUp
