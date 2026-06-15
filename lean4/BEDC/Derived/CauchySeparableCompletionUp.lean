import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchySeparableCompletionUp : Type where
  | mk (D T W R C E H K P N : BHist) : CauchySeparableCompletionUp

end BEDC.Derived
