import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactNetAdmission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead cover coverRead →
          PkgSig bundle coverRead pkg →
            UnaryHistory compactRead ∧ UnaryHistory coverRead ∧
              Cont compactMetric epsilonNet compactRead ∧ Cont compactRead cover coverRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle coverRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier compactRoute coverRoute coverPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactReadUnary coverUnary coverRoute
  exact ⟨compactReadUnary, coverReadUnary, compactRoute, coverRoute, provenancePkg, coverPkg⟩

end BEDC.Derived.CoveringdimensionUp
