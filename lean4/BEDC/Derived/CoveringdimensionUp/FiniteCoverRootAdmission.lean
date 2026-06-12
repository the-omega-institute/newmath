import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverRootAdmission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound rootRead →
        PkgSig bundle rootRead pkg →
          UnaryHistory compactMetric ∧ UnaryHistory cover ∧ UnaryHistory orderBound ∧
            UnaryHistory lebesgue ∧ UnaryHistory rootRead ∧
              Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
                Cont orderBound lebesgue replay ∧ Cont cover orderBound rootRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverOrderRoot rootPkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    compactEpsilonCover, coverRefinementOrder, orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary orderUnary coverOrderRoot
  exact
    ⟨compactUnary, coverUnary, orderUnary, lebesgueUnary, rootUnary, compactEpsilonCover,
      coverRefinementOrder, orderLebesgueReplay, coverOrderRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.CoveringdimensionUp
