import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetricCompletionAdmissibleEmbeddingUp : Type where
  | mk
      (metricCompletion completionEmbedding cauchyFilterBasis separatedMetric
        uniformContinuousExtension streamName regSeqRat dyadicRatCore realSeal
        transport replay provenance localName : BHist) :
      MetricCompletionAdmissibleEmbeddingUp
  deriving DecidableEq

end BEDC.Derived
