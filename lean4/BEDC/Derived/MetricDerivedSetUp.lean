import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetricDerivedSetUp : Type where
  | mk
      (metric subset puncturedBall streamWindows regularReadback realSeal transport replay provenance
        localName : BHist) :
      MetricDerivedSetUp
  deriving DecidableEq

end BEDC.Derived
