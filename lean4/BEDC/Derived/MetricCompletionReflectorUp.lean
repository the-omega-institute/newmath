import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetricCompletionReflectorUp : Type where
  | mk
      (metricCompletion uniformCompletion separatedMetric cauchyReflector realSealHandoff transport
        replay provenance name : BHist) :
      MetricCompletionReflectorUp
  deriving DecidableEq

end BEDC.Derived
