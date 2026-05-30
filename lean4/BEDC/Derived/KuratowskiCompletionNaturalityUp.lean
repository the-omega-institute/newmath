import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive KuratowskiCompletionNaturalityUp : Type where
  | mk
      (sourceMetric kuratowskiRoute metricConsumer reflectionWitness realReflectionSeal
        streamWindow dyadicLedger regularReadback transport replay provenance localName :
          BHist) :
      KuratowskiCompletionNaturalityUp
  deriving DecidableEq

end BEDC.Derived
