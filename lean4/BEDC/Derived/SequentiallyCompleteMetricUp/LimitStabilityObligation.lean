import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem SequentiallyCompleteMetricLimitStabilityObligation [AskSetup] [PackageSetup]
    {X S M L D H C P N X' S' M' L' D' H' C' P' N' metricRead metricRead'
      modulusRead modulusRead' limitRead limitRead' distanceRead distanceRead' replayRead
      replayRead' : BHist} :
    Cont X S metricRead -> Cont X' S' metricRead' ->
      Cont metricRead M modulusRead -> Cont metricRead' M' modulusRead' ->
        Cont modulusRead L limitRead -> Cont modulusRead' L' limitRead' ->
          Cont limitRead D distanceRead -> Cont limitRead' D' distanceRead' ->
            Cont distanceRead C replayRead -> Cont distanceRead' C' replayRead' ->
              hsame X X' -> hsame S S' -> hsame M M' -> hsame L L' ->
                hsame D D' -> hsame C C' ->
                  hsame limitRead limitRead' ∧ hsame distanceRead distanceRead' ∧
                    hsame replayRead replayRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame AskSetup PackageSetup
  intro metricRoute metricRoute' modulusRoute modulusRoute' limitRoute limitRoute'
    distanceRoute distanceRoute' replayRoute replayRoute' sameX sameS sameM sameL sameD sameC
  have sameMetricRead : hsame metricRead metricRead' :=
    cont_respects_hsame sameX sameS metricRoute metricRoute'
  have sameModulusRead : hsame modulusRead modulusRead' :=
    cont_respects_hsame sameMetricRead sameM modulusRoute modulusRoute'
  have sameLimitRead : hsame limitRead limitRead' :=
    cont_respects_hsame sameModulusRead sameL limitRoute limitRoute'
  have sameDistanceRead : hsame distanceRead distanceRead' :=
    cont_respects_hsame sameLimitRead sameD distanceRoute distanceRoute'
  have sameReplayRead : hsame replayRead replayRead' :=
    cont_respects_hsame sameDistanceRead sameC replayRoute replayRoute'
  exact And.intro sameLimitRead (And.intro sameDistanceRead sameReplayRead)

end BEDC.Derived.SequentiallyCompleteMetricUp
