import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyCompletionLiftUp : Type where
  | carrier (S T F U E K R H C P N : BHist) : CauchyCompletionLiftUp

end BEDC.Derived
