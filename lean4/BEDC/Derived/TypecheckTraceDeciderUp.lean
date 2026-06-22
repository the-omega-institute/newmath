import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TypecheckTraceDeciderUp : Type where
  | mk (G T Q B R H C P N : BHist) : TypecheckTraceDeciderUp

end BEDC.Derived
