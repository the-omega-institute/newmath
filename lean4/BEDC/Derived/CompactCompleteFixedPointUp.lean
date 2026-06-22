import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive CompactCompleteFixedPointUp : Type where
  | mk
      (compactMetric completeMetric continuousMap contraction orbit regSeqReadback realSeal transport
        replay provenance localName : BEDC.FKernel.Hist.BHist) :
      CompactCompleteFixedPointUp
  deriving DecidableEq

end BEDC.Derived
