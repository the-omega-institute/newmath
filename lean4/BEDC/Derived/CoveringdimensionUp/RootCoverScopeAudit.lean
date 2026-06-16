import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverScopeAudit [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName epsilonRead coverRead refinementRead lebesgueRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet epsilonRead →
        Cont epsilonRead cover coverRead →
          Cont coverRead refinement refinementRead →
            Cont refinementRead lebesgue lebesgueRead →
              Cont lebesgueRead orderBound consumerRead →
                PkgSig bundle consumerRead pkg →
                  UnaryHistory epsilonRead ∧ UnaryHistory coverRead ∧
                    UnaryHistory refinementRead ∧ UnaryHistory lebesgueRead ∧
                      UnaryHistory consumerRead ∧
                        Cont compactMetric epsilonNet epsilonRead ∧
                          Cont epsilonRead cover coverRead ∧
                            Cont coverRead refinement refinementRead ∧
                              Cont refinementRead lebesgue lebesgueRead ∧
                                Cont lebesgueRead orderBound consumerRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier compactEpsilonRead epsilonCoverRead coverRefinementRead
    refinementLebesgueRead lebesgueOrderConsumer consumerPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _compactEpsilonCover,
    _coverRefinementOrder, _orderLebesgueReplay, _transportReplayProvenance, provenancePkg,
    _localNamePkg⟩ := carrier
  have epsilonReadUnary : UnaryHistory epsilonRead :=
    unary_cont_closed compactUnary epsilonUnary compactEpsilonRead
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed epsilonReadUnary coverUnary epsilonCoverRead
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverReadUnary refinementUnary coverRefinementRead
  have lebesgueReadUnary : UnaryHistory lebesgueRead :=
    unary_cont_closed refinementReadUnary lebesgueUnary refinementLebesgueRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed lebesgueReadUnary orderUnary lebesgueOrderConsumer
  exact
    ⟨epsilonReadUnary, coverReadUnary, refinementReadUnary, lebesgueReadUnary,
      consumerReadUnary, compactEpsilonRead, epsilonCoverRead, coverRefinementRead,
      refinementLebesgueRead, lebesgueOrderConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.CoveringdimensionUp
