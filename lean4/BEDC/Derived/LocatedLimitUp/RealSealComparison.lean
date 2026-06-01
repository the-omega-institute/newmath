import BEDC.Derived.LocatedLimitUp.RealSealRoute
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem LocatedLimitCarrier_real_seal_comparison [AskSetup] [PackageSetup]
    {S M T Q S' M' T' Q' scheduleRead scheduleRead' readbackRead readbackRead'
      sealRead sealRead' : BHist}
    (sameS : hsame S S') (sameM : hsame M M') (sameT : hsame T T')
    (sameQ : hsame Q Q') (leftSchedule : Cont S M scheduleRead)
    (rightSchedule : Cont S' M' scheduleRead')
    (leftReadback : Cont scheduleRead T readbackRead)
    (rightReadback : Cont scheduleRead' T' readbackRead')
    (leftSeal : Cont readbackRead Q sealRead)
    (rightSeal : Cont readbackRead' Q' sealRead') :
    hsame scheduleRead scheduleRead' ∧ hsame readbackRead readbackRead' ∧
      hsame sealRead sealRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  have sameSchedule : hsame scheduleRead scheduleRead' :=
    cont_respects_hsame sameS sameM leftSchedule rightSchedule
  have sameReadback : hsame readbackRead readbackRead' :=
    cont_respects_hsame sameSchedule sameT leftReadback rightReadback
  have sameSeal : hsame sealRead sealRead' :=
    cont_respects_hsame sameReadback sameQ leftSeal rightSeal
  exact ⟨sameSchedule, sameReadback, sameSeal⟩

end BEDC.Derived.LocatedLimitUp
