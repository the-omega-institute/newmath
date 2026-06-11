import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverOrderNonescape [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName orderRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont orderBound lebesgue orderRead →
        Cont orderRead localName consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
              UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
                UnaryHistory orderRead ∧ UnaryHistory consumer ∧
                  Cont compactMetric epsilonNet cover ∧ Cont cover refinement orderBound ∧
                    Cont orderBound lebesgue orderRead ∧
                      Cont orderRead localName consumer ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier orderLebesgueRead localConsumer consumerPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed orderUnary lebesgueUnary orderLebesgueRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed orderReadUnary localNameUnary localConsumer
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
      orderReadUnary, consumerUnary, compactEpsilonCover, coverRefinementOrder,
      orderLebesgueRead, localConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.CoveringdimensionUp
