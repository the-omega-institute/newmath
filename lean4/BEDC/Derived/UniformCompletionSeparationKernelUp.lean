import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformCompletionSeparationKernelUp : Type where
  | mk
      (metricCompletion uniformCompletion separatedMetric cauchyFilter cauchyNet readback transport
        replay provenance name : BHist) :
      UniformCompletionSeparationKernelUp
  deriving DecidableEq

end BEDC.Derived
