import BEDC.Derived.LocatedLimitUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem LocatedLimit_regseqrat_readback_stability [AskSetup] [PackageSetup]
    {S M T Q E H C P N S' M' T' Q' scheduleRead scheduleRead' readbackRead
      readbackRead' : BHist}
    (sameS : hsame S S') (sameM : hsame M M') (sameT : hsame T T')
    (sameQ : hsame Q Q') (leftSchedule : Cont S M scheduleRead)
    (rightSchedule : Cont S' M' scheduleRead')
    (leftReadback : Cont scheduleRead T readbackRead)
    (rightReadback : Cont scheduleRead' T' readbackRead') :
    hsame scheduleRead scheduleRead' ∧ hsame readbackRead readbackRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  have sameSchedule : hsame scheduleRead scheduleRead' :=
    cont_respects_hsame sameS sameM leftSchedule rightSchedule
  have sameReadback : hsame readbackRead readbackRead' :=
    cont_respects_hsame sameSchedule sameT leftReadback rightReadback
  exact And.intro sameSchedule sameReadback

end BEDC.Derived.LocatedLimitUp
