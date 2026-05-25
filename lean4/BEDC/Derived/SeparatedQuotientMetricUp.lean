import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive SeparatedQuotientMetricUp : Type where
  | mk (X P Z S R E H C N : BEDC.FKernel.Hist.BHist) :
      SeparatedQuotientMetricUp
  deriving DecidableEq

end BEDC.Derived
