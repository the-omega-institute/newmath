import BEDC.FKernel.Hist

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Hist

inductive AnalyticContinuationSocketUp : Type where
  | mk
      (source leftOverlap witness operation output branch transport continuation provenance name :
        BHist) :
      AnalyticContinuationSocketUp

end BEDC.Derived.AnalyticContinuationSocketUp
