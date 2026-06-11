import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityCoverNonescape [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityRead coverRead escapeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover coverRead →
        Cont coverRead lebesgue densityRead →
          Cont densityRead localName escapeRead →
            PkgSig bundle escapeRead pkg →
              UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
                UnaryHistory lebesgue ∧ UnaryHistory densityRead ∧
                  UnaryHistory escapeRead ∧ Cont epsilonNet cover coverRead ∧
                    Cont coverRead lebesgue densityRead ∧
                      Cont densityRead localName escapeRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle escapeRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier epsilonCoverRead coverLebesgueDensity densityLocalEscape escapePkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverRead
  have densityReadUnary : UnaryHistory densityRead :=
    unary_cont_closed coverReadUnary lebesgueUnary coverLebesgueDensity
  have escapeReadUnary : UnaryHistory escapeRead :=
    unary_cont_closed densityReadUnary localNameUnary densityLocalEscape
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, lebesgueUnary, densityReadUnary,
      escapeReadUnary, epsilonCoverRead, coverLebesgueDensity, densityLocalEscape,
      provenancePkg, escapePkg⟩

end BEDC.Derived.CoveringdimensionUp
