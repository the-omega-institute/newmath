import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SeparatedCompletionReflectorUp : Type where
  | mk
      (metricCompletion separatedMetric uniformCompletion universalProperty cauchyFilter
        cauchyNet tolerance realSeal transport replay provenance name : BHist) :
      SeparatedCompletionReflectorUp
  deriving DecidableEq

end BEDC.Derived
