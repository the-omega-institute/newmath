import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TukeyDepthUp : Type where
  | mk (R X H S M W T C P N : BHist) : TukeyDepthUp

end BEDC.Derived
