import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_root_effective_metric_obligations [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName metricRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont target transport metricRead →
        Cont metricRead localName completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory metricRead ∧ UnaryHistory completionRead ∧
              Cont target transport metricRead ∧
                Cont metricRead localName completionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier targetTransportMetric metricLocalCompletion completionPkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, targetUnary, transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed targetUnary transportUnary targetTransportMetric
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary localNameUnary metricLocalCompletion
  exact
    ⟨metricUnary, completionUnary, targetTransportMetric, metricLocalCompletion,
      provenancePkg, completionPkg⟩

end BEDC.Derived.RepresentedSpaceUp
