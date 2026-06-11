import BEDC.Derived.CoveringdimensionUp.CompactNetOrderCarrier

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactNetOrderScope [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead refinement orderBound nerve transport replay provenance
      localName consumer scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCompactNetOrderCarrier compactMetric epsilonNet metricRead refinement
        orderBound nerve transport replay provenance localName bundle pkg →
      Cont replay localName consumer →
        Cont consumer nerve scopeRead →
          PkgSig bundle scopeRead pkg →
            UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧
              UnaryHistory metricRead ∧ UnaryHistory refinement ∧
                UnaryHistory orderBound ∧ UnaryHistory nerve ∧ UnaryHistory replay ∧
                  UnaryHistory consumer ∧ UnaryHistory scopeRead ∧
                    Cont compactMetric epsilonNet metricRead ∧
                      Cont metricRead refinement orderBound ∧
                        Cont orderBound nerve replay ∧ Cont replay localName consumer ∧
                          Cont consumer nerve scopeRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCompactNetOrderCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier replayLocalNameConsumer consumerNerveScopeRead scopePkg
  obtain ⟨compactUnary, epsilonUnary, metricReadUnary, refinementUnary, orderUnary,
    nerveUnary, _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    compactMetricRead, metricRefinementOrder, orderNerveReplay, provenancePkg,
    _localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayUnary localNameUnary replayLocalNameConsumer
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed consumerUnary nerveUnary consumerNerveScopeRead
  exact
    ⟨compactUnary, epsilonUnary, metricReadUnary, refinementUnary, orderUnary, nerveUnary,
      replayUnary, consumerUnary, scopeUnary, compactMetricRead, metricRefinementOrder,
      orderNerveReplay, replayLocalNameConsumer, consumerNerveScopeRead, provenancePkg,
      scopePkg⟩

end BEDC.Derived.CoveringdimensionUp
