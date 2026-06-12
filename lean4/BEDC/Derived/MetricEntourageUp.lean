import BEDC.FKernel.Hist

namespace BEDC.Derived.MetricEntourageUp

inductive MetricEntourageUp : Type
  | mk
      (M Q D B S T H C P N : _root_.BEDC.FKernel.Hist.BHist)
  deriving DecidableEq

end BEDC.Derived.MetricEntourageUp
