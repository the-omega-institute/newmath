import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive GaussMapUp : Type where
  | mk (R Z V F Q A E H C P N : BHist) : GaussMapUp

end BEDC.Derived
