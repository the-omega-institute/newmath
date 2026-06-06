import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem SequentiallyCompleteMetricClassifierTransport [AskSetup] [PackageSetup]
    {X S M L D C X' S' M' L' D' C' sequenceRead sequenceRead' modulusRead
      modulusRead' limitRead limitRead' distanceRead distanceRead' replayRead
      replayRead' : BHist} :
    hsame X X' → hsame S S' → hsame M M' → hsame L L' → hsame D D' →
      hsame C C' → Cont X S sequenceRead → Cont X' S' sequenceRead' →
        Cont sequenceRead M modulusRead → Cont sequenceRead' M' modulusRead' →
          Cont modulusRead L limitRead → Cont modulusRead' L' limitRead' →
            Cont limitRead D distanceRead → Cont limitRead' D' distanceRead' →
              Cont distanceRead C replayRead → Cont distanceRead' C' replayRead' →
                hsame replayRead replayRead' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro sameX sameS sameM sameL sameD sameC sequenceRoute sequenceRoute'
    modulusRoute modulusRoute' limitRoute limitRoute' distanceRoute distanceRoute'
    replayRoute replayRoute'
  cases sameX
  cases sameS
  cases sameM
  cases sameL
  cases sameD
  cases sameC
  cases sequenceRoute
  cases sequenceRoute'
  cases modulusRoute
  cases modulusRoute'
  cases limitRoute
  cases limitRoute'
  cases distanceRoute
  cases distanceRoute'
  cases replayRoute
  cases replayRoute'
  rfl

end BEDC.Derived.SequentiallyCompleteMetricUp
