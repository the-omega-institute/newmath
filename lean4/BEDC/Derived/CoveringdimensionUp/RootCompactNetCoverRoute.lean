import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCompactNetCoverRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRoot coverRead refinementRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRoot →
        Cont compactRoot cover coverRead →
          Cont coverRead refinement refinementRead →
            Cont refinementRead orderBound orderRead →
              PkgSig bundle orderRead pkg →
                UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
                  UnaryHistory refinement ∧ UnaryHistory orderBound ∧
                    UnaryHistory compactRoot ∧ UnaryHistory coverRead ∧
                      UnaryHistory refinementRead ∧ UnaryHistory orderRead ∧
                        Cont compactMetric epsilonNet compactRoot ∧
                          Cont compactRoot cover coverRead ∧
                            Cont coverRead refinement refinementRead ∧
                              Cont refinementRead orderBound orderRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle orderRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier compactRootRoute coverReadRoute refinementReadRoute orderReadRoute orderReadPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactRootUnary : UnaryHistory compactRoot :=
    unary_cont_closed compactUnary epsilonUnary compactRootRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactRootUnary coverUnary coverReadRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverReadUnary refinementUnary refinementReadRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementReadUnary orderUnary orderReadRoute
  exact ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    compactRootUnary, coverReadUnary, refinementReadUnary, orderReadUnary, compactRootRoute,
    coverReadRoute, refinementReadRoute, orderReadRoute, provenancePkg, orderReadPkg⟩

end BEDC.Derived.CoveringdimensionUp
