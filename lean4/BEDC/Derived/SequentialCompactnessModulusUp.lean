import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SequentialCompactnessModulusUp : Type where
  | mk
      (compactSource totalBounded completeMetric streamWindow dyadicTolerance regularReadback
        realSeal clusterHandoff transport replay provenance localName : BHist) :
      SequentialCompactnessModulusUp
  deriving DecidableEq

end BEDC.Derived
