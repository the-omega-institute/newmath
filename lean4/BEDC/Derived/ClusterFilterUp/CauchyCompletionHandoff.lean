import BEDC.Derived.ClusterFilterUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.ClusterFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ClusterFilterCarrier_cauchy_completion_handoff
    [AskSetup] [PackageSetup]
    {F M T W R E A H C P N filterMetric topologyWindow toleranceSeal adherentRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont F M filterMetric ->
      Cont T W topologyWindow ->
        Cont R E toleranceSeal ->
          Cont A C adherentRead ->
            Cont filterMetric topologyWindow consumer ->
              PkgSig bundle consumer pkg ->
                clusterFilterFromEventFlow
                    (clusterFilterToEventFlow (ClusterFilterUp.mk F M T W R E A H C P N)) =
                  some (ClusterFilterUp.mk F M T W R E A H C P N) ∧
                  Cont F M filterMetric ∧
                    Cont T W topologyWindow ∧
                      Cont R E toleranceSeal ∧
                        Cont A C adherentRead ∧
                          Cont filterMetric topologyWindow consumer ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro filterRoute topologyRoute toleranceRoute adherentRoute consumerRoute consumerPkg
  constructor
  · exact
      (ClusterFilterUpTasteGate_single_carrier_alignment).right.left
        (ClusterFilterUp.mk F M T W R E A H C P N)
  · exact
      ⟨filterRoute, topologyRoute, toleranceRoute, adherentRoute, consumerRoute,
        consumerPkg⟩

end BEDC.Derived.ClusterFilterUp
