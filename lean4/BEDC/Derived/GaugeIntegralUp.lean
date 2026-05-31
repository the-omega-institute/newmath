import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive GaugeIntegralUp : Type where
  | mk (I Gamma T S D Q R H C P N : BEDC.FKernel.Hist.BHist) : GaugeIntegralUp
  deriving DecidableEq

end BEDC.Derived
