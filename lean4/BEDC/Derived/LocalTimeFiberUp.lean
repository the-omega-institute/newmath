import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocalTimeFiberUp : Type where
  | mk
      (observerSource localStream localClockBudget synchronizationBoundary refusal transport replay
        provenance name : BHist) :
      LocalTimeFiberUp
  deriving DecidableEq

end BEDC.Derived
